module

public import RequestProject.Annulus

/-!
# Basic planar geometry for the quantitative overlap theorem

Coordinates in the plane, the quarter-turn `J`, orthonormal frames (which are
measure preserving), elementary facts about planks (center line, angle), and indexed
families of planks with their counting function, hole and excess-overlap cost.
-/

@[expose] public section

open MeasureTheory Set Metric Real
open scoped ENNReal

noncomputable section

namespace Annulus

/-! ### Numerical constants of the proof -/

/-- `ρ = 1/12`. -/
def kRho : ℝ := 1 / 12
/-- `τ = 10⁻⁴` (removability threshold). -/
def kTau : ℝ := 1e-4
/-- `δ = 10⁻⁴` (density threshold of dense disks). -/
def kDelta : ℝ := 1e-4
/-- `A = 10¹³` (angle–width separation). -/
def kA : ℝ := 1e13
/-- `γ = 10⁻⁹` (price of a removable pair). -/
def kGamma : ℝ := 1e-9

lemma kRho_pos : 0 < kRho := by norm_num [kRho]

/-! ### Coordinates -/

lemma inner_eq_coord (x y : Plane) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

lemma norm_sq_eq_coord (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two]

lemma norm_eq_coord (x : Plane) : ‖x‖ = √(x 0 ^ 2 + x 1 ^ 2) := by
  rw [← norm_sq_eq_coord, Real.sqrt_sq (norm_nonneg _)]

/-- The quarter turn `J(x₀, x₁) = (-x₁, x₀)`. -/
def J (x : Plane) : Plane := WithLp.toLp 2 ![-x 1, x 0]

@[simp] lemma J_apply_zero (x : Plane) : J x 0 = -x 1 := by simp [J]
@[simp] lemma J_apply_one (x : Plane) : J x 1 = x 0 := by simp [J]

lemma ext_coord {x y : Plane} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  ext i; fin_cases i <;> simp [h0, h1]

lemma J_add (x y : Plane) : J (x + y) = J x + J y := by
  apply ext_coord <;> simp; ring

lemma J_smul (a : ℝ) (x : Plane) : J (a • x) = a • J x := by
  apply ext_coord <;> simp

lemma J_neg (x : Plane) : J (-x) = -J x := by
  apply ext_coord <;> simp

lemma J_sub (x y : Plane) : J (x - y) = J x - J y := by
  apply ext_coord <;> simp; ring

lemma J_J (x : Plane) : J (J x) = -x := by
  apply ext_coord <;> simp

lemma inner_J_self (x : Plane) : inner ℝ (J x) x = 0 := by
  rw [inner_eq_coord]; simp; ring

lemma inner_self_J (x : Plane) : inner ℝ x (J x) = 0 := by
  rw [real_inner_comm, inner_J_self]

lemma inner_J_J (x y : Plane) : inner ℝ (J x) (J y) = inner ℝ x y := by
  rw [inner_eq_coord, inner_eq_coord]; simp; ring

lemma inner_J_left (x y : Plane) : inner ℝ (J x) y = -inner ℝ x (J y) := by
  rw [inner_eq_coord, inner_eq_coord]; simp

lemma norm_J (x : Plane) : ‖J x‖ = ‖x‖ := by
  rw [norm_eq_coord, norm_eq_coord]; simp [add_comm]

/-- In the plane, `⟪x,y⟫² + ⟪Jx,y⟫² = ‖x‖²‖y‖²`. -/
lemma inner_sq_add_inner_J_sq (x y : Plane) :
    inner ℝ x y ^ 2 + inner ℝ (J x) y ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  rw [inner_eq_coord, inner_eq_coord, norm_sq_eq_coord, norm_sq_eq_coord]; simp; ring

/-- Decomposition of a vector in the orthonormal frame `(e, Je)`. -/
lemma decomp_frame {e : Plane} (he : ‖e‖ = 1) (x : Plane) :
    x = inner ℝ x e • e + inner ℝ x (J e) • J e := by
  have h := norm_sq_eq_coord e
  rw [he] at h
  apply ext_coord
  · simp [inner_eq_coord]; linear_combination (x 0) * h
  · simp [inner_eq_coord]; linear_combination (x 1) * h

/-! ### Orthonormal frames -/

/-- The frame map `(u, v) ↦ c + u e + v Je`. -/
def frame (c e : Plane) (p : ℝ × ℝ) : Plane := c + p.1 • e + p.2 • J e

/-- The inverse coordinates of the frame. -/
def frameInv (c e : Plane) (x : Plane) : ℝ × ℝ := (inner ℝ (x - c) e, inner ℝ (x - c) (J e))

lemma frameInv_frame {c e : Plane} (he : ‖e‖ = 1) (p : ℝ × ℝ) :
    frameInv c e (frame c e p) = p := by
  have h1 : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have h2 : inner ℝ (J e) (J e) = 1 := by rw [inner_J_J, h1]
  simp only [frameInv, frame]
  rw [show c + p.1 • e + p.2 • J e - c = p.1 • e + p.2 • J e by abel]
  ext <;> simp [inner_add_left, inner_smul_left, inner_J_self, inner_self_J, he, norm_J]

lemma frame_frameInv {c e : Plane} (he : ‖e‖ = 1) (x : Plane) :
    frame c e (frameInv c e x) = x := by
  simp only [frame, frameInv]
  rw [add_assoc, ← decomp_frame he (x - c)]
  abel

/-- The frame as a measurable equivalence. -/
def frameEquiv (c e : Plane) (he : ‖e‖ = 1) : ℝ × ℝ ≃ᵐ Plane where
  toFun := frame c e
  invFun := frameInv c e
  left_inv := frameInv_frame he
  right_inv := frame_frameInv he
  measurable_toFun := by
    change Measurable (fun p : ℝ × ℝ => c + p.1 • e + p.2 • J e); fun_prop
  measurable_invFun := by
    unfold frameInv
    exact (Continuous.prodMk ((continuous_id.sub continuous_const).inner continuous_const)
      ((continuous_id.sub continuous_const).inner continuous_const)).measurable

@[simp] lemma frameEquiv_apply (c e : Plane) (he : ‖e‖ = 1) (p : ℝ × ℝ) :
    frameEquiv c e he p = frame c e p := rfl

/-- The linear part of the frame, as a linear isometry of the plane. -/
def rotLin (e : Plane) : Plane →ₗ[ℝ] Plane where
  toFun x := x 0 • e + x 1 • J e
  map_add' x y := by simp [add_smul]; abel
  map_smul' a x := by simp [smul_add, smul_smul]

lemma rotLin_inner {e : Plane} (he : ‖e‖ = 1) (x y : Plane) :
    inner ℝ (rotLin e x) (rotLin e y) = inner ℝ x y := by
  have h1 : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have h2 : inner ℝ (J e) (J e) = 1 := by rw [inner_J_J, h1]
  simp only [rotLin, LinearMap.coe_mk, AddHom.coe_mk, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, inner_J_self, inner_self_J, h1, h2,
    RCLike.conj_to_real]
  rw [inner_eq_coord]; ring

theorem measurePreserving_frame (c e : Plane) (he : ‖e‖ = 1) :
    MeasurePreserving (frame c e) volume volume := by
  let L : Plane ≃ₗᵢ[ℝ] Plane :=
    (LinearMap.isometryOfInner (rotLin e) (rotLin_inner he)).toLinearIsometryEquiv rfl
  let E : Plane ≃ᵐ ℝ × ℝ := (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans
    MeasurableEquiv.finTwoArrow
  have hE : MeasurePreserving E volume volume :=
    (volume_preserving_finTwoArrow ℝ).comp
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))
  have hEs : MeasurePreserving E.symm volume volume := hE.symm
  have hL : MeasurePreserving L volume volume := L.measurePreserving
  have hT : MeasurePreserving (fun x : Plane => c + x) volume volume :=
    measurePreserving_add_left volume c
  have hcomp := hT.comp (hL.comp hEs)
  convert hcomp using 1
  funext p
  simp only [Function.comp_apply]
  have : L (E.symm p) = p.1 • e + p.2 • J e := by
    rfl
  rw [this, frame, add_assoc]

lemma volume_frame_preimage (c e : Plane) (he : ‖e‖ = 1) (S : Set Plane) :
    volume (frame c e ⁻¹' S) = volume S := by
  have h : MeasurePreserving (frameEquiv c e he) volume volume := measurePreserving_frame c e he
  exact h.measure_preimage_equiv S

lemma volume_eq_frame_preimage (c e : Plane) (he : ‖e‖ = 1) (S : Set Plane) :
    volume S = volume (frame c e ⁻¹' S) := (volume_frame_preimage c e he S).symm

/-! ### Strips -/

/-- A strip of half-width `t` around the line `⟪x,n⟫ = m`, intersected with a disk of
radius `R`, has area at most `4Rt`. -/
lemma volume_strip_inter_ball_le {n : Plane} (hn : ‖n‖ = 1) (m t : ℝ) (c : Plane) (R : ℝ) :
    volume ({x : Plane | |inner ℝ x n - m| ≤ t} ∩ closedBall c R) ≤
      ENNReal.ofReal (4 * R * t) := by
  set e : Plane := -J n with he_def
  have he : ‖e‖ = 1 := by rw [he_def, norm_neg, norm_J, hn]
  have hJe : J e = n := by rw [he_def, J_neg, J_J, neg_neg]
  rw [volume_eq_frame_preimage 0 e he]
  have hsub : frame 0 e ⁻¹' ({x : Plane | |inner ℝ x n - m| ≤ t} ∩ closedBall c R) ⊆
      Icc (inner ℝ c e - R) (inner ℝ c e + R) ×ˢ Icc (m - t) (m + t) := by
    intro p hp
    simp only [mem_preimage, mem_inter_iff, mem_setOf_eq, mem_closedBall] at hp
    obtain ⟨h1, h2⟩ := hp
    have hin : frameInv 0 e (frame 0 e p) = p := frameInv_frame he p
    have hp1 : inner ℝ (frame 0 e p) e = p.1 := by
      have := congrArg Prod.fst hin; simpa [frameInv] using this
    have hp2 : inner ℝ (frame 0 e p) n = p.2 := by
      have := congrArg Prod.snd hin; simpa [frameInv, hJe] using this
    rw [hp2] at h1
    have h3 : |inner ℝ (frame 0 e p - c) e| ≤ R := by
      calc |inner ℝ (frame 0 e p - c) e| ≤ ‖frame 0 e p - c‖ * ‖e‖ := abs_real_inner_le_norm _ _
        _ ≤ R := by rw [he, mul_one, ← dist_eq_norm]; exact h2
    rw [inner_sub_left, hp1] at h3
    simp only [mem_prod, mem_Icc]
    constructor
    · constructor <;> linarith [abs_le.1 h3]
    · constructor <;> linarith [abs_le.1 h1]
  refine (measure_mono hsub).trans ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  rcases lt_or_ge t 0 with ht | ht
  · rw [ENNReal.ofReal_of_nonpos (p := m + t - (m - t)) (by linarith), mul_zero]
    exact zero_le
  rcases lt_or_ge R 0 with hR | hR
  · rw [ENNReal.ofReal_of_nonpos (p := inner ℝ c e + R - (inner ℝ c e - R)) (by linarith),
      zero_mul]
    exact zero_le
  rw [← ENNReal.ofReal_mul (by linarith)]
  apply ENNReal.ofReal_le_ofReal; nlinarith

/-! ### Planks -/

namespace Plank

/-- The offset `(a + b)/2` of the center line. -/
def mid (P : Plank) : ℝ := (P.a + P.b) / 2

/-- The center line `ℓ_P = {x : ⟪x, n⟫ = (a + b)/2}`. -/
def centerLine (P : Plank) : Set Plane := {x | inner ℝ x P.n = P.mid}

/-- The acute angle between the center lines of two planks (`0` if parallel). -/
def ang (P Q : Plank) : ℝ := Real.arccos |inner ℝ P.n Q.n|

lemma width_nonneg (P : Plank) : 0 ≤ P.width := by
  have := P.a_le_b; unfold width; linarith

lemma mem_carrier_iff (P : Plank) (x : Plane) :
    x ∈ P.carrier ↔ |inner ℝ x P.n - P.mid| ≤ P.width / 2 := by
  simp only [carrier, mem_setOf_eq, mid, width, abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

lemma carrier_eq (P : Plank) :
    P.carrier = {x | |inner ℝ x P.n - P.mid| ≤ P.width / 2} := by
  ext x; exact P.mem_carrier_iff x

lemma ang_comm (P Q : Plank) : P.ang Q = Q.ang P := by
  rw [ang, ang, real_inner_comm]

lemma ang_nonneg (P Q : Plank) : 0 ≤ P.ang Q := Real.arccos_nonneg _

lemma abs_inner_n_le (P Q : Plank) : |inner ℝ P.n Q.n| ≤ 1 := by
  have := abs_real_inner_le_norm P.n Q.n
  rwa [P.norm_n, Q.norm_n, mul_one] at this

lemma ang_le (P Q : Plank) : P.ang Q ≤ π / 2 := by
  rw [ang, Real.arccos_le_pi_div_two]; exact abs_nonneg _

lemma cos_ang (P Q : Plank) : Real.cos (P.ang Q) = |inner ℝ P.n Q.n| := by
  rw [ang, Real.cos_arccos (by linarith [abs_nonneg (inner ℝ P.n Q.n)]) (P.abs_inner_n_le Q)]

lemma sin_ang (P Q : Plank) : Real.sin (P.ang Q) = |inner ℝ (J P.n) Q.n| := by
  rw [ang, Real.sin_arccos, sq_abs]
  have h := inner_sq_add_inner_J_sq P.n Q.n
  rw [P.norm_n, Q.norm_n] at h
  rw [show 1 - inner ℝ P.n Q.n ^ 2 = inner ℝ (J P.n) Q.n ^ 2 by nlinarith,
    Real.sqrt_sq_eq_abs]

end Plank

/-! ### Indexed families of planks -/

section Families

variable {ι : Type*} [Fintype ι]

open Classical in
/-- The counting function `M_𝒫(x) = #{i : x ∈ P_i}` of an indexed family. -/
def countF (P : ι → Plank) (x : Plane) : ℕ :=
  (Finset.univ.filter fun i => x ∈ (P i).carrier).card

/-- The excess-overlap cost `I(𝒫) = ∫_D (M_𝒫 - 1)₊` of an indexed family. -/
def excessF (P : ι → Plank) : ℝ≥0∞ := ∫⁻ x in unitDisk, ((countF P x : ℝ≥0∞) - 1)

/-- The hole `H(𝒫) = D \ ⋃ P_i` of an indexed family. -/
def holeF (P : ι → Plank) : Set Plane := unitDisk \ ⋃ i, (P i).carrier

lemma countF_eq_sum (P : ι → Plank) (x : Plane) :
    (countF P x : ℝ≥0∞) = ∑ i, (P i).carrier.indicator 1 x := by
  classical
  simp only [countF, Finset.card_filter, Nat.cast_sum, Set.indicator_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp

lemma measurable_countF (P : ι → Plank) : Measurable (fun x => (countF P x : ℝ≥0∞)) := by
  simp_rw [countF_eq_sum]
  exact Finset.measurable_sum _ (fun i _ => measurable_one.indicator (P i).measurableSet_carrier)

lemma count_eq_countF (F : Finset Plank) (x : Plane) :
    count F x = countF (fun P : F => P.1) x := by
  classical
  simp only [count, countF]
  rw [← Finset.card_map ⟨(Subtype.val : F → Plank), Subtype.val_injective⟩]
  congr 1
  ext P
  simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hP, hx⟩; exact ⟨⟨P, hP⟩, hx, rfl⟩
  · rintro ⟨⟨Q, hQ⟩, hx, rfl⟩; exact ⟨hQ, hx⟩

lemma excess_eq_excessF (F : Finset Plank) : excess F = excessF (fun P : F => P.1) := by
  simp only [excess, excessF, count_eq_countF]

lemma hole_eq_holeF (F : Finset Plank) : hole F = holeF (fun P : F => P.1) := by
  simp only [hole, holeF]
  congr 1
  ext x
  simp

end Families

end Annulus

end
