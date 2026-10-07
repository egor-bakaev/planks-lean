module

public import RequestProject.Overlap.Defs

/-!
# The dense region is controlled by the excess (Vitali covering)
-/

@[expose] public section

open MeasureTheory Set Metric Real
open scoped ENNReal

noncomputable section

namespace Annulus

variable {ι : Type*} [Fintype ι]

lemma denseRegion_subset_unitDisk (P : ι → Plank) (δ : ℝ) : denseRegion P δ ⊆ unitDisk := by
  intro x hx
  simp only [denseRegion, mem_iUnion] at hx
  obtain ⟨c, t, ht, hx⟩ := hx
  exact ht.2.1 hx

lemma isOpen_denseRegion (P : ι → Plank) (δ : ℝ) : IsOpen (denseRegion P δ) := by
  unfold denseRegion
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball

/-- A ball contained in the unit disk has radius at most `1`. -/
lemma radius_le_one_of_ball_subset {c : Plane} {s : ℝ} (h : ball c s ⊆ unitDisk) : s ≤ 1 := by
  by_contra hs
  push_neg at hs
  set v : Plane := EuclideanSpace.single 0 1
  have hv : ‖v‖ = 1 := by simp [v]
  set t := (1 + s) / 2
  have ht1 : 1 < t := by simp only [t]; linarith
  have hts : t < s := by simp only [t]; linarith
  have hin : ∀ y, ‖y - c‖ < s → ‖y‖ ≤ 1 := fun y hy => by
    have := h (show y ∈ ball c s by rwa [mem_ball, dist_eq_norm])
    simpa [unitDisk] using this
  have h1 := hin (c + t • v) (by simp [norm_smul, hv, abs_of_pos (by linarith : (0:ℝ) < t), hts])
  have h2 := hin (c - t • v) (by simp [norm_smul, hv, abs_of_pos (by linarith : (0:ℝ) < t), hts])
  have h3 : ‖(c + t • v) - (c - t • v)‖ ≤ ‖c + t • v‖ + ‖c - t • v‖ := norm_sub_le _ _
  have h4 : ‖(c + t • v) - (c - t • v)‖ = 2 * t := by
    rw [show (c + t • v) - (c - t • v) = (2 * t) • v by rw [mul_smul]; module]
    rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
  linarith

/-- `δ |U_δ| ≤ 25 I(𝒫)`, from the Vitali `5r`-covering lemma. -/
theorem volume_denseRegion_le (P : ι → Plank) (δ : ℝ) :
    ENNReal.ofReal δ * volume (denseRegion P δ) ≤ 25 * excessF P := by
  set t : Set (Plane × ℝ) := {p | IsDenseDisk P δ p.1 p.2}
  obtain ⟨u, hut, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun p : Plane × ℝ => ball p.1 p.2) t (fun p => p.2) 2 one_lt_two
    (fun a ha => (show IsDenseDisk P δ a.1 a.2 from ha).1.le) 1
    (fun a ha => radius_le_one_of_ball_subset (show IsDenseDisk P δ a.1 a.2 from ha).2.1)
    (fun a ha => nonempty_ball.2 (show IsDenseDisk P δ a.1 a.2 from ha).1)
  have hu_count : u.Countable := hdisj.countable_of_nonempty_interior fun a ha => by
    rw [isOpen_ball.interior_eq]; exact nonempty_ball.2 (hut ha).1
  have hU : denseRegion P δ ⊆ ⋃ b ∈ u, ball b.1 (5 * b.2) := by
    intro y hy
    simp only [denseRegion, mem_iUnion] at hy
    obtain ⟨c, s, hcs, hy⟩ := hy
    obtain ⟨b, hbu, ⟨z, hz1, hz2⟩, hle⟩ := hcov (c, s) hcs
    simp only [mem_iUnion]
    refine ⟨b, hbu, ?_⟩
    simp only [mem_ball] at hy hz1 hz2 ⊢
    calc dist y b.1 ≤ dist y c + dist c z + dist z b.1 := dist_triangle4 _ _ _ _
      _ < s + s + b.2 := by rw [dist_comm c z]; gcongr
      _ ≤ 5 * b.2 := by simp only at hle; linarith
  have hball5 : ∀ b : Plane × ℝ, b ∈ u → volume (ball b.1 (5 * b.2)) = 25 * volume (ball b.1 b.2) := by
    intro b hb
    rw [Measure.addHaar_ball_mul_of_pos volume b.1 (by norm_num : (0 : ℝ) < 5),
      Measure.addHaar_ball_center volume b.1 b.2, finrank_euclideanSpace_fin]
    congr 1
    rw [show ((5 : ℝ) ^ 2) = ((25 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
    norm_num
  have hdense : ∀ b ∈ u, ENNReal.ofReal δ * volume (ball b.1 b.2) ≤
      ∫⁻ x in ball b.1 b.2, ((countF P x : ℝ≥0∞) - 1) := fun b hb => (hut hb).2.2.le
  calc ENNReal.ofReal δ * volume (denseRegion P δ)
      ≤ ENNReal.ofReal δ * ∑' b : u, volume (ball b.1.1 (5 * b.1.2)) := by
        gcongr
        exact (measure_mono hU).trans (measure_biUnion_le _ hu_count _)
    _ = ∑' b : u, 25 * (ENNReal.ofReal δ * volume (ball b.1.1 b.1.2)) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun b => ?_
        rw [hball5 b.1 b.2]; ring
    _ ≤ ∑' b : u, 25 * ∫⁻ x in ball b.1.1 b.1.2, ((countF P x : ℝ≥0∞) - 1) := by
        gcongr with b
        exact hdense b.1 b.2
    _ = 25 * ∫⁻ x in ⋃ b ∈ u, ball b.1 b.2, ((countF P x : ℝ≥0∞) - 1) := by
        rw [ENNReal.tsum_mul_left, lintegral_biUnion hu_count (fun _ _ => measurableSet_ball) hdisj]
    _ ≤ 25 * excessF P := by
        gcongr
        refine lintegral_mono_set ?_
        intro y hy
        simp only [mem_iUnion] at hy
        obtain ⟨b, hb, hy⟩ := hy
        exact (hut hb).2.1 hy

end Annulus

end
