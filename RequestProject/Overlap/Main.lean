module

public import RequestProject.Overlap.Approx

/-!
# The quantitative overlap theorem (Theorem 2.1) and Bezdek's theorem

`overlap_theorem` states Theorem 2.1 with an explicit positive constant.  The unconditional
form of Bezdek's annulus theorem follows from it through the reduction of Section 7.
-/

@[expose] public section

open MeasureTheory Set Metric Real

noncomputable section

namespace Annulus

/-- Theorem 2.1 (quantitative overlap theorem): there are constants `c > 0` and
`r_ov > 0` such that `I(𝒫) ≥ (c/r)|H(𝒫)|` whenever `H(𝒫) ⊆ rD` with `0 < r < r_ov`. -/
theorem overlap_theorem : ∃ c > 0, OverlapTheoremWith c :=
  ⟨cEq, cEq_pos, overlap_theorem_cEq⟩

/-- Bezdek's annulus theorem, unconditional form. -/
theorem bezdek_annulus' :
    ∃ rStar > 0, ∀ F : Finset Plank,
      unitDisk \ closedBall 0 rStar ⊆ ⋃ P ∈ F, P.carrier → 2 ≤ ∑ P ∈ F, P.width := by
  obtain ⟨c, hc, h⟩ := overlap_theorem
  exact bezdek_annulus_of_overlap hc h

end Annulus

end
