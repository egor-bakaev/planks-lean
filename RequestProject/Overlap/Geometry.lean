module

public import RequestProject.Overlap.Defs

/-!
# Elementary planar geometry for the overlap theorem

Angle and sine facts for center lines, intersection of two lines, and the
distance from a point to a center line.
-/

@[expose] public section

open MeasureTheory Set Metric Real
open scoped ENNReal

noncomputable section

namespace Annulus

/-! ### Unit vectors -/

lemma unit_coord {a : Plane} (ha : ‖a‖ = 1) : a 0 ^ 2 + a 1 ^ 2 = 1 := by
  have := norm_sq_eq_coord a; rw [ha] at this; linarith

/-- `sin(C - A) = sin(B - A) cos(C - B) + cos(B - A) sin(C - B)` in vector form. -/
lemma inner_J_decomp {a b : Plane} (hb : ‖b‖ = 1) (c : Plane) :
    inner ℝ (J a) c = inner ℝ (J a) b * inner ℝ b c + inner ℝ a b * inner ℝ (J b) c := by
  have hb' := unit_coord hb
  simp only [inner_eq_coord, J_apply_zero, J_apply_one]
  linear_combination (a 1 * c 0 - a 0 * c 1) * hb'

lemma abs_inner_J_triangle {a b : Plane} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (c : Plane)
    (hc : ‖c‖ = 1) :
    |inner ℝ (J a) c| ≤ |inner ℝ (J a) b| + |inner ℝ (J b) c| := by
  rw [inner_J_decomp hb c]
  have h1 : |inner ℝ b c| ≤ 1 := by
    have := abs_real_inner_le_norm b c; rwa [hb, hc, mul_one] at this
  have h2 : |inner ℝ a b| ≤ 1 := by
    have := abs_real_inner_le_norm a b; rwa [ha, hb, mul_one] at this
  calc |inner ℝ (J a) b * inner ℝ b c + inner ℝ a b * inner ℝ (J b) c|
      ≤ |inner ℝ (J a) b * inner ℝ b c| + |inner ℝ a b * inner ℝ (J b) c| := abs_add_le _ _
    _ = |inner ℝ (J a) b| * |inner ℝ b c| + |inner ℝ a b| * |inner ℝ (J b) c| := by
        rw [abs_mul, abs_mul]
    _ ≤ |inner ℝ (J a) b| * 1 + 1 * |inner ℝ (J b) c| := by
        gcongr
    _ = _ := by ring

lemma inner_J_comm_abs (a b : Plane) : |inner ℝ (J a) b| = |inner ℝ (J b) a| := by
  simp only [inner_eq_coord, J_apply_zero, J_apply_one]
  rw [← abs_neg]; ring_nf

lemma norm_sq_frame {e : Plane} (he : ‖e‖ = 1) (x : Plane) :
    ‖x‖ ^ 2 = inner ℝ x e ^ 2 + inner ℝ x (J e) ^ 2 := by
  have h := inner_sq_add_inner_J_sq e x
  rw [he, one_pow, one_mul] at h
  rw [← h, real_inner_comm e x, real_inner_comm (J e) x]

/-! ### Sines -/

lemma sin_add_le_add {x y : ℝ} (hx : 0 ≤ x) (hx' : x ≤ π / 2) (hy : 0 ≤ y) (hy' : y ≤ π / 2) :
    Real.sin (x + y) ≤ Real.sin x + Real.sin y := by
  rw [Real.sin_add]
  have h1 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx (by linarith [pi_pos])
  have h2 : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy (by linarith [pi_pos])
  have h3 : Real.cos x ≤ 1 := Real.cos_le_one x
  have h4 : Real.cos y ≤ 1 := Real.cos_le_one y
  nlinarith

lemma sin_le_sin_of_le' {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ π / 2) :
    Real.sin x ≤ Real.sin y :=
  Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hy hxy

/-- If `0 ≤ x < 2β` with `x, β ≤ π/2`, then `sin x ≤ 2 sin β`. -/
lemma sin_le_two_sin {x β : ℝ} (hx : 0 ≤ x) (hx' : x ≤ π / 2) (hβ' : β ≤ π / 2)
    (hxβ : x ≤ 2 * β) : Real.sin x ≤ 2 * Real.sin β := by
  have hβ : 0 ≤ β := by linarith
  have hsβ : 0 ≤ Real.sin β := Real.sin_nonneg_of_nonneg_of_le_pi hβ (by linarith [pi_pos])
  rcases le_total x β with h | h
  · have := sin_le_sin_of_le' hx h hβ'; linarith
  · have e : x = (x - β) + β := by ring
    rw [e]
    refine (sin_add_le_add (by linarith) (by linarith) hβ hβ').trans ?_
    have := sin_le_sin_of_le' (x := x - β) (y := β) (by linarith) (by linarith) hβ'
    linarith

/-- Jordan's inequality `2x/π ≤ sin x` on `[0, π/2]`. -/
lemma two_div_pi_mul_le_sin {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ π / 2) :
    2 / π * x ≤ Real.sin x := by
  have := Real.mul_le_sin hx hx'
  linarith

lemma sin_le_self' {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x := Real.sin_le hx

/-! ### Rectangles -/

/-- A set containing the frame image of a coordinate rectangle has at least its area. -/
lemma le_volume_of_frame_rect {c e : Plane} (he : ‖e‖ = 1) {S : Set Plane} {a b a' b' : ℝ}
    (hab : a ≤ b) (hS : ∀ p : ℝ × ℝ, p.1 ∈ Icc a b → p.2 ∈ Icc a' b' → frame c e p ∈ S) :
    ENNReal.ofReal ((b - a) * (b' - a')) ≤ volume S := by
  rw [volume_eq_frame_preimage c e he S]
  calc ENNReal.ofReal ((b - a) * (b' - a')) ≤ volume (Icc a b ×ˢ Icc a' b') := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
          ← ENNReal.ofReal_mul (by linarith)]
    _ ≤ volume (frame c e ⁻¹' S) := measure_mono fun p hp => hS p hp.1 hp.2

lemma frame_inner_e {c e : Plane} (he : ‖e‖ = 1) (p : ℝ × ℝ) :
    inner ℝ (frame c e p - c) e = p.1 := by
  have h1 : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  rw [show frame c e p - c = p.1 • e + p.2 • J e by simp only [frame]; abel]
  simp only [inner_add_left, inner_smul_left, h1, inner_J_self, RCLike.conj_to_real]
  ring

lemma frame_inner_Je {c e : Plane} (he : ‖e‖ = 1) (p : ℝ × ℝ) :
    inner ℝ (frame c e p - c) (J e) = p.2 := by
  have h1 : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have h2 : inner ℝ (J e) (J e) = 1 := by rw [inner_J_J, h1]
  rw [show frame c e p - c = p.1 • e + p.2 • J e by simp only [frame]; abel]
  simp only [inner_add_left, inner_smul_left, h2, inner_self_J, RCLike.conj_to_real]
  ring

lemma norm_frame_sub_sq {c e : Plane} (he : ‖e‖ = 1) (p : ℝ × ℝ) :
    ‖frame c e p - c‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  rw [norm_sq_frame he, frame_inner_e he, frame_inner_Je he]

/-! ### Angles between planks -/

namespace Plank

lemma sin_ang_eq (P Q : Plank) : Real.sin (P.ang Q) = |inner ℝ (J P.n) Q.n| := P.sin_ang Q

lemma inner_sq_add (P Q : Plank) : inner ℝ P.n Q.n ^ 2 + inner ℝ (J P.n) Q.n ^ 2 = 1 := by
  have h := inner_sq_add_inner_J_sq P.n Q.n
  rwa [P.norm_n, Q.norm_n, one_pow, one_mul] at h

lemma ang_ne_zero_iff (P Q : Plank) : P.ang Q ≠ 0 ↔ inner ℝ (J P.n) Q.n ≠ 0 := by
  have h1 := P.abs_inner_n_le Q
  have h2 := P.inner_sq_add Q
  rw [ang, Ne, Real.arccos_eq_zero]
  constructor
  · intro h h'
    apply h
    rw [h'] at h2
    have : |inner ℝ P.n Q.n| ^ 2 = 1 := by rw [sq_abs]; linarith
    nlinarith [abs_nonneg (inner ℝ P.n Q.n)]
  · intro h h'
    apply h
    have : |inner ℝ P.n Q.n| = 1 := le_antisymm h1 h'
    have h3 : inner ℝ P.n Q.n ^ 2 = 1 := by rw [← sq_abs, this, one_pow]
    have : inner ℝ (J P.n) Q.n ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

lemma sin_ang_pos {P Q : Plank} (h : P.ang Q ≠ 0) : 0 < |inner ℝ (J P.n) Q.n| :=
  abs_pos.2 ((P.ang_ne_zero_iff Q).1 h)

lemma sin_ang_le_one (P Q : Plank) : |inner ℝ (J P.n) Q.n| ≤ 1 := by
  have := abs_real_inner_le_norm (J P.n) Q.n
  rwa [norm_J, P.norm_n, Q.norm_n, mul_one] at this

lemma mem_centerLine {P : Plank} {x : Plane} : x ∈ P.centerLine ↔ inner ℝ x P.n = P.mid :=
  Iff.rfl

/-- On the center line, a point is determined by its coordinate along the line. -/
lemma eq_of_mem_centerLine {P : Plank} {x : Plane} (hx : x ∈ P.centerLine) :
    x = P.mid • P.n + inner ℝ x (J P.n) • J P.n := by
  have := decomp_frame P.norm_n x
  rw [mem_centerLine.1 hx] at this
  exact this

lemma norm_sq_of_mem_centerLine {P : Plank} {x : Plane} (hx : x ∈ P.centerLine) :
    ‖x‖ ^ 2 = P.mid ^ 2 + inner ℝ x (J P.n) ^ 2 := by
  rw [norm_sq_frame P.norm_n x, mem_centerLine.1 hx]

lemma abs_mid_le_of_mem_carrier {P : Plank} {x : Plane} (hx : x ∈ P.carrier) :
    |P.mid| ≤ ‖x‖ + P.width / 2 := by
  rw [P.mem_carrier_iff] at hx
  have h1 : |inner ℝ x P.n| ≤ ‖x‖ := by
    have := abs_real_inner_le_norm x P.n; rwa [P.norm_n, mul_one] at this
  have := abs_sub_abs_le_abs_sub P.mid (inner ℝ x P.n)
  rw [abs_sub_comm] at this
  linarith

/-- Two nonparallel center lines meet at the explicit point below. -/
def crossPt (P Q : Plank) : Plane :=
  P.mid • P.n + ((Q.mid - P.mid * inner ℝ P.n Q.n) / inner ℝ (J P.n) Q.n) • J P.n

lemma crossPt_mem_left (P Q : Plank) : P.crossPt Q ∈ P.centerLine := by
  have h1 : inner ℝ P.n P.n = 1 := by rw [real_inner_self_eq_norm_sq, P.norm_n]; norm_num
  simp only [mem_centerLine, crossPt, inner_add_left, inner_smul_left, h1, inner_J_self,
    RCLike.conj_to_real]
  ring

lemma crossPt_mem_right {P Q : Plank} (h : P.ang Q ≠ 0) : P.crossPt Q ∈ Q.centerLine := by
  have hs := (P.ang_ne_zero_iff Q).1 h
  simp only [mem_centerLine, crossPt, inner_add_left, inner_smul_left, RCLike.conj_to_real]
  field_simp
  ring

lemma norm_crossPt_le {P Q : Plank} (h : P.ang Q ≠ 0) :
    ‖P.crossPt Q‖ ≤ |P.mid| + (|Q.mid| + |P.mid|) / |inner ℝ (J P.n) Q.n| := by
  have hs := P.sin_ang_pos h
  have hc : |inner ℝ P.n Q.n| ≤ 1 := P.abs_inner_n_le Q
  unfold crossPt
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, P.norm_n, norm_J, P.norm_n, mul_one, mul_one, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_div]
  gcongr
  calc |Q.mid - P.mid * inner ℝ P.n Q.n| ≤ |Q.mid| + |P.mid * inner ℝ P.n Q.n| := abs_sub _ _
    _ ≤ |Q.mid| + |P.mid| := by
        rw [abs_mul]; gcongr; nlinarith [abs_nonneg P.mid]

/-- Uniqueness of the crossing point. -/
lemma eq_crossPt {P Q : Plank} (h : P.ang Q ≠ 0) {x : Plane} (hxP : x ∈ P.centerLine)
    (hxQ : x ∈ Q.centerLine) : x = P.crossPt Q := by
  have hs := (P.ang_ne_zero_iff Q).1 h
  have hx := eq_of_mem_centerLine hxP
  have hQ := mem_centerLine.1 hxQ
  rw [hx] at hQ
  simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real] at hQ
  rw [hx, crossPt]
  congr 2
  field_simp
  linarith

end Plank

end Annulus

end
