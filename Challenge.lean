module

public import Mathlib

/-!
# Comparator challenge: Bezdek's annulus theorem

Self-contained statement (depends only on Mathlib).  There is some `r > 0` such that
whenever finitely many planks `{x : |⟪x, uᵢ⟫ - aᵢ| ≤ wᵢ/2}` (unit normals `uᵢ`, widths
`wᵢ ≥ 0`) cover the closed annulus `r ≤ ‖x‖ ≤ 1`, their total width is at least `2`.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace

abbrev Plane := EuclideanSpace ℝ (Fin 2)

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
  sorry

end
