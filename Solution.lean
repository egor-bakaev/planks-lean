module

public import Mathlib
public import RequestProject.Overlap.Main

/-!
# Comparator solution: Bezdek's annulus theorem

The statement is identical to `Challenge.lean`.  It is derived from the
project's formalization:

* `bezdek_annulus_of_overlapTheorem`: the comparator statement follows from the quantitative
  overlap theorem `Annulus.OverlapTheoremWith c` for any constant `c > 0`;
* `bezdek_annulus` applies it to `Annulus.overlap_theorem`, the quantitative overlap theorem
  with an explicit positive constant.

Everything is proved; the only axioms used are `propext`, `Classical.choice` and
`Quot.sound`.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The comparator statement, assuming the quantitative overlap theorem. -/
theorem bezdek_annulus_of_overlapTheorem {c : ℝ} (hc : 0 < c)
    (hov : Annulus.OverlapTheoremWith c) :
    ∃ r : ℝ,
      0 < r ∧
      ∀ {n : ℕ}
        (u : Fin n → Plane)
        (a w : Fin n → ℝ),
        (∀ i, ‖u i‖ = 1) →
        (∀ i, 0 ≤ w i) →
        (∀ x : Plane,
          r ≤ ‖x‖ →
          ‖x‖ ≤ 1 →
          ∃ i,
            |⟪x, u i⟫_ℝ - a i| ≤ w i / 2) →
        2 ≤ ∑ i, w i := by
  classical
  obtain ⟨r, hr, hmain⟩ := Annulus.bezdek_annulus_of_overlap hc hov
  refine ⟨r, hr, fun {n} u a w hu hw hcov => ?_⟩
  let pl : Fin n → Annulus.Plank := fun i =>
    ⟨u i, hu i, a i - w i / 2, a i + w i / 2, by linarith [hw i]⟩
  have hwidth : ∀ i, (pl i).width = w i := fun i => by
    simp only [Annulus.Plank.width, pl]; ring
  have h2 := hmain (Finset.univ.image pl) (by
    intro x hx
    obtain ⟨hxD, hxr⟩ := hx
    simp only [Annulus.unitDisk, Metric.mem_closedBall, dist_zero_right, not_le] at hxD hxr
    obtain ⟨i, hi⟩ := hcov x hxr.le hxD
    simp only [Set.mem_iUnion, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨pl i, ⟨i, rfl⟩, ?_⟩
    simp only [Annulus.Plank.carrier, Set.mem_ofPred_eq, pl]
    constructor <;> linarith [(abs_le.1 hi).1, (abs_le.1 hi).2])
  calc (2 : ℝ) ≤ ∑ P ∈ Finset.univ.image pl, P.width := h2
    _ ≤ ∑ i, (pl i).width :=
        Finset.sum_image_le_of_nonneg (fun P _ => P.width_nonneg)
    _ = ∑ i, w i := Finset.sum_congr rfl (fun i _ => hwidth i)

/-- Bezdek's annulus theorem in the comparator form. -/
theorem bezdek_annulus :
    ∃ r : ℝ,
      0 < r ∧
      ∀ {n : ℕ}
        (u : Fin n → Plane)
        (a w : Fin n → ℝ),
        (∀ i, ‖u i‖ = 1) →
        (∀ i, 0 ≤ w i) →
        (∀ x : Plane,
          r ≤ ‖x‖ →
          ‖x‖ ≤ 1 →
          ∃ i,
            |⟪x, u i⟫_ℝ - a i| ≤ w i / 2) →
        2 ≤ ∑ i, w i := by
  obtain ⟨c, hc, hov⟩ := Annulus.overlap_theorem
  exact bezdek_annulus_of_overlapTheorem hc hov

end
