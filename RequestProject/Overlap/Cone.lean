module

public import RequestProject.Overlap.Basic

/-!
# Convex cone estimate

If a convex set `C` contains a point `v` far from the origin, then `C` is much larger than its
part `C ∩ rD`: the homothetic copies `v + t (C ∩ rD - v)` for suitable `t ∈ [1/2, 1]` are
contained in `C` and pairwise disjoint.
-/

@[expose] public section

open MeasureTheory Set Metric Real
open scoped ENNReal

noncomputable section

namespace Annulus

lemma homothety_image_eq_preimage (v : Plane) {t : ℝ} (ht : t ≠ 0) (K : Set Plane) :
    AffineMap.homothety v t '' K = AffineMap.homothety v t⁻¹ ⁻¹' K := by
  ext y
  simp only [mem_image, mem_preimage, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  constructor
  · rintro ⟨x, hx, rfl⟩
    convert hx using 1
    rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ ht, one_smul, sub_add_cancel]
  · intro hy
    refine ⟨_, hy, ?_⟩
    rw [add_sub_cancel_right, smul_smul, mul_inv_cancel₀ ht, one_smul, sub_add_cancel]

set_option maxHeartbeats 1000000 in
/-- Convex cone estimate via disjoint homothetic copies. -/
theorem cone_estimate {C : Set Plane} (hC : Convex ℝ C) {r L : ℝ} (hr : 0 < r) (hL : 1 ≤ L)
    (hK : MeasurableSet (C ∩ closedBall 0 r)) {v : Plane} (hv : v ∈ C)
    (hvn : 32 * L * r < ‖v‖) :
    ENNReal.ofReal (2 * L) * volume (C ∩ closedBall 0 r) ≤ volume C := by
  classical
  set K := C ∩ closedBall 0 r with hK_def
  set N : ℕ := ⌈8 * L⌉₊ with hN_def
  have hN : 8 * L ≤ N := Nat.le_ceil _
  have hN' : (N : ℝ) < 8 * L + 1 := Nat.ceil_lt_add_one (by linarith)
  have hN2 : (2 : ℝ) ≤ N := by linarith
  set δ : ℝ := 1 / (2 * ((N : ℝ) - 1)) with hδ_def
  have hδ0 : 0 < δ := by rw [hδ_def]; apply div_pos one_pos; linarith
  have hδN : ((N : ℝ) - 1) * δ = 1 / 2 := by
    have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
    rw [hδ_def]; field_simp
  set t : ℕ → ℝ := fun i => 1 - i * δ with ht_def
  have ht : ∀ i ∈ Finset.range N, 1 / 2 ≤ t i ∧ t i ≤ 1 := by
    intro i hi
    have hi' : (i : ℝ) ≤ N - 1 := by
      have := Finset.mem_range.1 hi
      have : (i : ℝ) + 1 ≤ N := by exact_mod_cast this
      linarith
    refine ⟨?_, ?_⟩
    · have := mul_le_mul_of_nonneg_right hi' hδ0.le
      simp only [t]; linarith
    · simp only [t]; nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  set X : ℕ → Set Plane := fun i => AffineMap.homothety v (t i) '' K with hX_def
  have hXpt : ∀ i x, AffineMap.homothety v (t i) x = t i • x + (1 - t i) • v := by
    intro i x
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul,
      one_smul]
    abel
  have hXC : ∀ i ∈ Finset.range N, X i ⊆ C := by
    rintro i hi _ ⟨x, hx, rfl⟩
    rw [hXpt]
    obtain ⟨h1, h2⟩ := ht i hi
    exact hC hx.1 hv (by linarith) (by linarith) (by ring)
  have hXball : ∀ i ∈ Finset.range N, X i ⊆ closedBall ((i * δ) • v) r := by
    rintro i hi _ ⟨x, hx, rfl⟩
    rw [hXpt, mem_closedBall, dist_eq_norm]
    obtain ⟨h1, h2⟩ := ht i hi
    have e : t i • x + (1 - t i) • v - (i * δ) • v = t i • x := by
      simp only [t]; module
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hxr : ‖x‖ ≤ r := by simpa using hx.2
    nlinarith [norm_nonneg x]
  have hdisj : (↑(Finset.range N) : Set ℕ).PairwiseDisjoint X := by
    intro i hi j hj hij
    rw [Function.onFun, Set.disjoint_left]
    intro y hyi hyj
    have h1 := hXball i hi hyi
    have h2 := hXball j hj hyj
    rw [mem_closedBall, dist_eq_norm] at h1 h2
    have h3 : ‖(i * δ) • v - (j * δ) • v‖ ≤ 2 * r := by
      calc ‖(i * δ) • v - (j * δ) • v‖ = ‖(y - (j * δ) • v) - (y - (i * δ) • v)‖ := by
            congr 1; abel
        _ ≤ ‖y - (j * δ) • v‖ + ‖y - (i * δ) • v‖ := norm_sub_le _ _
        _ ≤ 2 * r := by linarith
    have e : (i * δ) • v - (j * δ) • v = (((i : ℝ) - j) * δ) • v := by module
    rw [e, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hδ0] at h3
    have hij' : (1 : ℝ) ≤ |(i : ℝ) - j| := by
      have : (i : ℤ) ≠ j := by exact_mod_cast hij
      have h : (1 : ℤ) ≤ |(i : ℤ) - j| := Int.one_le_abs (sub_ne_zero.2 this)
      have : ((|(i : ℤ) - j| : ℤ) : ℝ) = |(i : ℝ) - j| := by push_cast; ring_nf
      rw [← this]; exact_mod_cast h
    have hv' : 2 * r < δ * ‖v‖ := by
      have : 4 * r * ((N : ℝ) - 1) < ‖v‖ := by nlinarith
      have e2 : δ * ‖v‖ = ‖v‖ / (2 * ((N : ℝ) - 1)) := by rw [hδ_def]; ring
      rw [e2, lt_div_iff₀ (by linarith)]; linarith
    have : δ * ‖v‖ ≤ |(i : ℝ) - j| * δ * ‖v‖ := by
      have := mul_le_mul_of_nonneg_right hij' (mul_nonneg hδ0.le (norm_nonneg v))
      linarith
    linarith
  have hmeas : ∀ i ∈ Finset.range N, MeasurableSet (X i) := by
    intro i hi
    have hti : t i ≠ 0 := by linarith [(ht i hi).1]
    simp only [X]
    rw [homothety_image_eq_preimage v hti]
    exact (AffineMap.homothety v (t i)⁻¹).continuous_of_finiteDimensional.measurable hK
  have hvol : ∀ i, volume (X i) = ENNReal.ofReal (t i ^ 2) * volume K := by
    intro i
    simp only [X]
    rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin, abs_of_nonneg (sq_nonneg _)]
  calc ENNReal.ofReal (2 * L) * volume K
      ≤ ∑ i ∈ Finset.range N, ENNReal.ofReal (1 / 4) * volume K := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _
    _ ≤ ∑ i ∈ Finset.range N, volume (X i) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [hvol]
        gcongr
        have := (ht i hi).1
        nlinarith
    _ = volume (⋃ i ∈ Finset.range N, X i) := (measure_biUnion_finset hdisj hmeas).symm
    _ ≤ volume C := measure_mono (iUnion₂_subset hXC)

end Annulus

end
