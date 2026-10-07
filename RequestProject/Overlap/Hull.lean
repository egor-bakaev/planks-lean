module

public import RequestProject.Overlap.Geometry

/-!
# The candidate hull `K₀ = conv(J_P ∪ J_Q)`

* every line meeting the hull meets one of the two chords;
* the hull lies in a strip of half-width `2ρ sin β` around `ℓ_P`, so `|K₀| ≤ 8ρ² sin β`;
* the hull contains a rectangle of size `1.2ρ × 0.11ρ sin β` next to `ℓ_P`
  (Lemma 4.6), so `|K₀| ≥ 0.132ρ² sin β`.
-/

@[expose] public section

open MeasureTheory Set Metric Real
open scoped ENNReal

noncomputable section

namespace Annulus

lemma mem_chord {P : Plank} {x : Plane} :
    x ∈ chord P ↔ inner ℝ x P.n = P.mid ∧ ‖x‖ ≤ kRho := by
  simp [chord, Plank.centerLine, mem_closedBall, dist_zero_right]

lemma convex_chord (P : Plank) : Convex ℝ (chord P) := by
  refine Convex.inter ?_ (convex_closedBall _ _)
  intro x hx y hy a b ha hb hab
  simp only [Plank.centerLine, mem_setOf_eq] at hx hy ⊢
  rw [inner_add_left, inner_smul_left, inner_smul_left, hx, hy]
  simp only [RCLike.conj_to_real]
  rw [← add_mul, hab, one_mul]

lemma chord_subset_hull_left (P Q : Plank) : chord P ⊆ hull P Q :=
  subset_union_left.trans (subset_convexHull ℝ _)

lemma chord_subset_hull_right (P Q : Plank) : chord Q ⊆ hull P Q :=
  subset_union_right.trans (subset_convexHull ℝ _)

/-- Any line `{⟨x, m⟩ = k}` meeting the hull meets one of the two chords, provided the
chords share a point. -/
lemma exists_chord_of_mem_hull {P Q : Plank} {c : Plane} (hcP : c ∈ chord P)
    (hcQ : c ∈ chord Q) (m : Plane) {y : Plane} (hy : y ∈ hull P Q) :
    ∃ z ∈ chord P ∪ chord Q, inner ℝ z m = inner ℝ y m := by
  by_contra hcon
  push_neg at hcon
  set k := inner ℝ y m
  set g : Plane → ℝ := fun z => inner ℝ z m - k
  have hg0 : ∀ z ∈ chord P ∪ chord Q, g z ≠ 0 := fun z hz h =>
    hcon z hz (by simp only [g] at h; linarith)
  -- same sign as at `c` along each chord
  have hsign : ∀ S : Set Plane, Convex ℝ S → c ∈ S → S ⊆ chord P ∪ chord Q →
      ∀ z ∈ S, 0 < g z * g c := by
    intro S hS hcS hSsub z hz
    by_contra hneg
    push_neg at hneg
    have hz0 := hg0 z (hSsub hz)
    have hc0 := hg0 c (hSsub hcS)
    have hlt : g z * g c < 0 := lt_of_le_of_ne hneg (mul_ne_zero hz0 hc0)
    set t := g c / (g c - g z)
    have hden : g c - g z ≠ 0 := by
      intro h; rw [sub_eq_zero] at h; rw [h] at hlt; nlinarith [sq_nonneg (g c)]
    have ht0 : 0 ≤ t := by
      rcases lt_or_gt_of_ne hc0 with h | h
      · have : g z > 0 := by
          by_contra h'; push_neg at h'; nlinarith
        exact div_nonneg_of_nonpos h.le (by linarith)
      · have : g z < 0 := by
          by_contra h'; push_neg at h'; nlinarith
        exact div_nonneg h.le (by linarith)
    have ht1 : t ≤ 1 := by
      rcases lt_or_gt_of_ne hc0 with h | h
      · have : g z > 0 := by
          by_contra h'; push_neg at h'; nlinarith
        rw [div_le_one_of_neg (by linarith)]; linarith
      · have : g z < 0 := by
          by_contra h'; push_neg at h'; nlinarith
        rw [div_le_one (by linarith)]; linarith
    have hmem : (1 - t) • c + t • z ∈ S := hS hcS hz (by linarith) ht0 (by ring)
    apply hg0 _ (hSsub hmem)
    simp only [g, inner_add_left, inner_smul_left, RCLike.conj_to_real]
    have : inner ℝ c m = g c + k := by simp only [g]; ring
    have h2 : inner ℝ z m = g z + k := by simp only [g]; ring
    rw [this, h2]
    simp only [t]
    field_simp
    ring
  have hall : ∀ z ∈ chord P ∪ chord Q, 0 < g z * g c := by
    rintro z (hz | hz)
    · exact hsign _ (convex_chord P) hcP subset_union_left z hz
    · exact hsign _ (convex_chord Q) hcQ subset_union_right z hz
  -- the open half-plane `{g · g c > 0}` is convex and contains both chords
  have hconv : Convex ℝ {z : Plane | 0 < g z * g c} := by
    intro x hx z hz a b ha hb hab
    simp only [mem_setOf_eq, g] at hx hz ⊢
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    have : a * inner ℝ x m + b * inner ℝ z m - k =
        a * (inner ℝ x m - k) + b * (inner ℝ z m - k) := by
      linear_combination k * hab
    rw [this, add_mul, mul_assoc, mul_assoc]
    rcases ha.lt_or_eq with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb hz.le)
    · subst ha'
      simp only [zero_add] at hab
      subst hab
      simpa using hz
  have hsub : hull P Q ⊆ {z : Plane | 0 < g z * g c} :=
    convexHull_min (fun z hz => hall z hz) hconv
  have := hsub hy
  simp only [mem_setOf_eq, g, k, sub_self, zero_mul] at this
  exact lt_irrefl 0 this

/-- Points of the second chord are within `2ρ sin β` of `ℓ_P`. -/
lemma chord_subset_strip {P Q : Plank} {c : Plane} (hcP : c ∈ P.centerLine)
    (hcQ : c ∈ chord Q) :
    chord Q ⊆ {x | |inner ℝ x P.n - P.mid| ≤ 2 * kRho * |inner ℝ (J P.n) Q.n|} := by
  intro x hx
  rw [mem_chord] at hx hcQ
  simp only [mem_setOf_eq]
  have hxc : x - c = inner ℝ (x - c) (J Q.n) • J Q.n := by
    have := decomp_frame Q.norm_n (x - c)
    rw [inner_sub_left, hx.1, hcQ.1, sub_self, zero_smul, zero_add] at this
    exact this
  have h1 : inner ℝ x P.n - P.mid = inner ℝ (x - c) P.n := by
    rw [inner_sub_left, Plank.mem_centerLine.1 hcP]
  rw [h1, hxc, inner_smul_left, RCLike.conj_to_real, abs_mul]
  have h2 : |inner ℝ (x - c) (J Q.n)| ≤ 2 * kRho := by
    have := abs_real_inner_le_norm (x - c) (J Q.n)
    rw [norm_J, Q.norm_n, mul_one] at this
    refine this.trans ((norm_sub_le _ _).trans ?_)
    linarith [hx.2, hcQ.2]
  have h3 : |inner ℝ (J Q.n) P.n| = |inner ℝ (J P.n) Q.n| := inner_J_comm_abs _ _
  rw [h3]
  exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)

lemma hull_subset_strip {P Q : Plank} {c : Plane} (hcP : c ∈ chord P) (hcQ : c ∈ chord Q) :
    hull P Q ⊆ closedBall 0 kRho ∩
      {x | |inner ℝ x P.n - P.mid| ≤ 2 * kRho * |inner ℝ (J P.n) Q.n|} := by
  refine convexHull_min ?_ ((convex_closedBall _ _).inter ?_)
  · rintro x (hx | hx)
    · rw [mem_chord] at hx
      refine ⟨by simpa using hx.2, ?_⟩
      simp only [mem_setOf_eq, hx.1, sub_self, abs_zero]
      exact mul_nonneg (by linarith [kRho_pos]) (abs_nonneg _)
    · refine ⟨by rw [mem_chord] at hx; simpa using hx.2, ?_⟩
      exact chord_subset_strip hcP.1 hcQ hx
  · intro x hx y hy a b ha hb hab
    simp only [mem_setOf_eq] at hx hy ⊢
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    have : a * inner ℝ x P.n + b * inner ℝ y P.n - P.mid =
        a * (inner ℝ x P.n - P.mid) + b * (inner ℝ y P.n - P.mid) := by
      linear_combination P.mid * hab
    rw [this]
    calc |a * (inner ℝ x P.n - P.mid) + b * (inner ℝ y P.n - P.mid)|
        ≤ a * |inner ℝ x P.n - P.mid| + b * |inner ℝ y P.n - P.mid| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * (2 * kRho * |inner ℝ (J P.n) Q.n|) + b * (2 * kRho * |inner ℝ (J P.n) Q.n|) := by
          gcongr
      _ = _ := by rw [← add_mul, hab, one_mul]

/-- `|K₀| ≤ 8 ρ² sin β`. -/
lemma volume_hull_le {P Q : Plank} {c : Plane} (hcP : c ∈ chord P) (hcQ : c ∈ chord Q) :
    volume (hull P Q) ≤ ENNReal.ofReal (8 * kRho ^ 2 * |inner ℝ (J P.n) Q.n|) := by
  refine (measure_mono (hull_subset_strip hcP hcQ)).trans ?_
  rw [inter_comm]
  refine (volume_strip_inter_ball_le P.norm_n P.mid _ 0 kRho).trans ?_
  apply ENNReal.ofReal_le_ofReal
  nlinarith [kRho_pos]

set_option maxHeartbeats 1000000 in
/-- Lemma 4.6 (rectangle inside the hull). -/
lemma rect_mem_hull {P Q : Plank} (hP : |P.mid| ≤ 7 / 100 * kRho) (hQ : |Q.mid| ≤ 3 / 4 * kRho)
    {c : Plane} (hcP : c ∈ P.centerLine) (hcQ : c ∈ Q.centerLine)
    (hs : 0 < |inner ℝ (J P.n) Q.n|) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ u v : ℝ, |u| ≤ 3 / 5 * kRho → 0 ≤ v →
      v ≤ 11 / 100 * kRho * |inner ℝ (J P.n) Q.n| →
      P.mid • P.n + u • J P.n + (σ * v) • P.n ∈ hull P Q := by
  have hρ := kRho_pos
  set s := |inner ℝ (J P.n) Q.n| with hs_def
  set n := P.n
  set e := J P.n
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, P.norm_n]; norm_num
  have hen : inner ℝ e n = 0 := inner_J_self _
  have hee : inner ℝ e e = 1 := by rw [inner_J_J]; exact hnn
  have hne : inner ℝ n e = 0 := inner_self_J _
  -- far endpoint of the second chord
  set tc := inner ℝ c (J Q.n)
  set b0 := √(kRho ^ 2 - Q.mid ^ 2)
  have hQsq : Q.mid ^ 2 ≤ (3 / 4 * kRho) ^ 2 := by rw [← sq_abs]; gcongr
  have hb0sq : b0 ^ 2 = kRho ^ 2 - Q.mid ^ 2 := Real.sq_sqrt (by nlinarith)
  have hb0 : 66 / 100 * kRho ≤ b0 := by
    rw [show 66 / 100 * kRho = √((66 / 100 * kRho) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    nlinarith
  set ε : ℝ := if 0 ≤ tc then -1 else 1
  set E : Plane := Q.mid • Q.n + (ε * b0) • J Q.n
  have hQnn : inner ℝ Q.n Q.n = 1 := by rw [real_inner_self_eq_norm_sq, Q.norm_n]; norm_num
  have hEchord : E ∈ chord Q := by
    rw [mem_chord]
    constructor
    · simp only [E, inner_add_left, inner_smul_left, hQnn, inner_J_self, RCLike.conj_to_real]
      ring
    · have : ‖E‖ ^ 2 = kRho ^ 2 := by
        rw [norm_sq_frame Q.norm_n E]
        simp only [E, inner_add_left, inner_smul_left, hQnn, inner_J_self, inner_self_J,
          inner_J_J, RCLike.conj_to_real]
        have hε : ε ^ 2 = 1 := by simp only [ε]; split_ifs <;> norm_num
        nlinarith
      rw [← abs_of_nonneg (norm_nonneg E), ← abs_of_pos hρ]
      exact (sq_eq_sq_iff_abs_eq_abs _ _).1 this |>.le
  have hEnorm : ‖E‖ ≤ kRho := (mem_chord.1 hEchord).2
  have hc_eq : c = Q.mid • Q.n + tc • J Q.n := Plank.eq_of_mem_centerLine hcQ
  have hEc : E - c = (ε * b0 - tc) • J Q.n := by
    rw [hc_eq]; simp only [E]; rw [sub_smul]; abel
  have hgap : b0 ≤ |ε * b0 - tc| := by
    simp only [ε]
    split_ifs with h
    · rw [abs_of_nonpos (by nlinarith)]; linarith
    · push_neg at h; rw [abs_of_pos (by nlinarith)]; linarith
  set H0 := inner ℝ (E - c) n
  have hH0 : H0 = (ε * b0 - tc) * inner ℝ (J Q.n) n := by
    simp only [H0]; rw [hEc, inner_smul_left, RCLike.conj_to_real]
  have hJQ : |inner ℝ (J Q.n) n| = s := inner_J_comm_abs _ _
  have hH0abs : b0 * s ≤ |H0| := by
    rw [hH0, abs_mul, hJQ]; exact mul_le_mul_of_nonneg_right hgap (abs_nonneg _)
  have hH0pos : 0 < |H0| := lt_of_lt_of_le (mul_pos (by linarith) hs) hH0abs
  set σ : ℝ := if 0 < H0 then 1 else -1
  have hσH : σ * H0 = |H0| := by
    simp only [σ]; split_ifs with h
    · rw [abs_of_pos h, one_mul]
    · push_neg at h; rw [abs_of_nonpos h]; ring
  have hσsq : σ * σ = 1 := by simp only [σ]; split_ifs <;> norm_num
  refine ⟨σ, by simp only [σ]; split_ifs <;> simp, fun u v hu hv hvs => ?_⟩
  set y := P.mid • n + u • e + (σ * v) • n
  set lam := v / |H0|
  have hlam0 : 0 ≤ lam := div_nonneg hv hH0pos.le
  have hlam1 : lam ≤ 1 / 6 := by
    rw [div_le_iff₀ hH0pos]
    have : 11 / 100 * kRho * s ≤ 1 / 6 * (b0 * s) := by nlinarith
    linarith
  have hlamH : lam * H0 = σ * v := by
    have hH0eq : H0 = σ * |H0| := by rw [← hσH, ← mul_assoc, hσsq, one_mul]
    calc lam * H0 = v / |H0| * (σ * |H0|) := by rw [← hH0eq]
      _ = σ * v := by field_simp
  set z : Plane := (1 - lam)⁻¹ • (y - lam • E)
  have hyz : y = lam • E + (1 - lam) • z := by
    simp only [z]; rw [smul_smul, mul_inv_cancel₀ (by linarith), one_smul]; abel
  have hEn : inner ℝ E n = P.mid + H0 := by
    simp only [H0]; rw [inner_sub_left, Plank.mem_centerLine.1 hcP]; ring
  have hyn : inner ℝ y n = P.mid + σ * v := by
    simp only [y, inner_add_left, inner_smul_left, hnn, hen, RCLike.conj_to_real]; ring
  have hye : inner ℝ y e = u := by
    simp only [y, inner_add_left, inner_smul_left, hne, hee, RCLike.conj_to_real]; ring
  have hzn : inner ℝ z n = P.mid := by
    simp only [z, inner_smul_left, inner_sub_left, hyn, hEn, RCLike.conj_to_real]
    rw [mul_add, hlamH]
    have h1l : 1 - lam ≠ 0 := by linarith
    field_simp
    ring
  have hEe : |inner ℝ E e| ≤ kRho := by
    have := abs_real_inner_le_norm E e
    rw [norm_J, P.norm_n, mul_one] at this; linarith
  have hze : |inner ℝ z e| ≤ 92 / 100 * kRho := by
    simp only [z, inner_smul_left, inner_sub_left, hye, RCLike.conj_to_real]
    rw [abs_mul, abs_inv, abs_of_pos (by linarith : (0 : ℝ) < 1 - lam)]
    rw [inv_mul_le_iff₀ (by linarith)]
    calc |u - lam * inner ℝ E e| ≤ |u| + lam * |inner ℝ E e| := by
          refine (abs_sub _ _).trans ?_; rw [abs_mul, abs_of_nonneg hlam0]
      _ ≤ 3 / 5 * kRho + lam * kRho := add_le_add hu (mul_le_mul_of_nonneg_left hEe hlam0)
      _ ≤ (1 - lam) * (92 / 100 * kRho) := by
          linarith [mul_le_mul_of_nonneg_right hlam1 hρ.le]
  have hzchord : z ∈ chord P := by
    rw [mem_chord]
    refine ⟨hzn, ?_⟩
    have h1 : ‖z‖ ^ 2 = P.mid ^ 2 + inner ℝ z e ^ 2 := by
      rw [norm_sq_frame P.norm_n z, hzn]
    have h2 : P.mid ^ 2 ≤ (7 / 100 * kRho) ^ 2 := by rw [← sq_abs]; gcongr
    have h3 : inner ℝ z e ^ 2 ≤ (92 / 100 * kRho) ^ 2 := by rw [← sq_abs]; gcongr
    have h4 : (7 / 100 * kRho) ^ 2 + (92 / 100 * kRho) ^ 2 ≤ kRho ^ 2 := by
      have : 0 ≤ kRho ^ 2 := sq_nonneg _
      ring_nf; linarith
    have : ‖z‖ ^ 2 ≤ kRho ^ 2 := by rw [h1]; linarith
    exact (sq_le_sq₀ (norm_nonneg z) hρ.le).mp this
  rw [hyz]
  exact convex_convexHull ℝ _ (chord_subset_hull_right P Q hEchord)
    (chord_subset_hull_left P Q hzchord) hlam0 (by linarith) (by ring)

lemma J_smul_J (σ : ℝ) (n : Plane) : J (-σ • J n) = σ • n := by
  rw [J_smul, J_J]; module

lemma norm_neg_smul_J {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {n : Plane} (hn : ‖n‖ = 1) :
    ‖-σ • J n‖ = 1 := by
  rw [norm_smul, norm_J, hn, mul_one, Real.norm_eq_abs, abs_neg]
  rcases hσ with rfl | rfl <;> simp

/-- `|K₀| ≥ 0.132 ρ² sin β`. -/
lemma volume_hull_ge {P Q : Plank} (hP : |P.mid| ≤ 7 / 100 * kRho) (hQ : |Q.mid| ≤ 3 / 4 * kRho)
    {c : Plane} (hcP : c ∈ P.centerLine) (hcQ : c ∈ Q.centerLine)
    (hs : 0 < |inner ℝ (J P.n) Q.n|) :
    ENNReal.ofReal (132 / 1000 * kRho ^ 2 * |inner ℝ (J P.n) Q.n|) ≤ volume (hull P Q) := by
  obtain ⟨σ, hσ, hrect⟩ := rect_mem_hull hP hQ hcP hcQ hs
  have hρ := kRho_pos
  have h := le_volume_of_frame_rect (c := P.mid • P.n) (norm_neg_smul_J hσ P.norm_n)
    (S := hull P Q) (a := -(3 / 5 * kRho)) (b := 3 / 5 * kRho) (a' := 0)
    (b' := 11 / 100 * kRho * |inner ℝ (J P.n) Q.n|) (by linarith) (fun p hp1 hp2 => by
      have hu : |-σ * p.1| ≤ 3 / 5 * kRho := by
        rw [abs_mul, abs_neg]
        rcases hσ with rfl | rfl <;> simp [abs_le] <;> constructor <;> linarith [hp1.1, hp1.2]
      have := hrect (-σ * p.1) p.2 hu hp2.1 hp2.2
      simp only [frame, J_smul_J]
      convert this using 1
      rw [smul_smul, smul_smul]
      module)
  refine le_trans (le_of_eq ?_) h
  congr 1; ring

end Annulus

end
