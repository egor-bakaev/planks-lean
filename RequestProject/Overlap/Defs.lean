module

public import RequestProject.Overlap.Basic

/-!
# Definitions for pruning and dense overlap

Deep and central planks, candidate and removable pairs, final pruning families, the final
hole, and `δ`-dense disks with the dense region `U_δ`.  All notions are computed from a
fixed indexed base family `P : ι → Plank`.

Compared with the notes, the hull used in the removability condition is the convex hull
`K₀ = conv(J_P ∪ J_Q)` of the two chords `J_P = ℓ_P ∩ ρD`, `J_Q = ℓ_Q ∩ ρD`
(rather than the convex hull of the plank pieces).  Both the pruning theorem and the price
estimate for removable pairs go through with this choice.
-/

@[expose] public section

open MeasureTheory Set Metric Real
open scoped ENNReal

noncomputable section

namespace Annulus

/-- A plank is *deep* if its center line is within `0.75 ρ` of the origin. -/
def IsDeep (P : Plank) : Prop := |P.mid| ≤ 3 / 4 * kRho

/-- A plank is *central* if its center line is within `0.07 ρ` of the origin. -/
def IsCentral (P : Plank) : Prop := |P.mid| ≤ 7 / 100 * kRho

/-- The center lines of `P` and `Q` meet in a single point, of norm at most `R`. -/
def CrossIn (P Q : Plank) (R : ℝ) : Prop :=
  P.ang Q ≠ 0 ∧ ∃ x : Plane, ‖x‖ ≤ R ∧ x ∈ P.centerLine ∧ x ∈ Q.centerLine

/-- The chord `J_P = ℓ_P ∩ ρD`. -/
def chord (P : Plank) : Set Plane := P.centerLine ∩ closedBall 0 kRho

/-- The hull `K₀(P,Q) = conv(J_P ∪ J_Q)`. -/
def hull (P Q : Plank) : Set Plane := convexHull ℝ (chord P ∪ chord Q)

section Family

variable {ι : Type*} [Fintype ι]

/-- All members of the family have the common width `w`. -/
def EqualWidth (P : ι → Plank) (w : ℝ) : Prop := ∀ i, (P i).width = w

/-- The angle–width hypothesis `ang(P,Q) ≥ A w / ρ` for nonparallel members. -/
def AngleSep (P : ι → Plank) (w : ℝ) : Prop :=
  ∀ i j, (P i).ang (P j) ≠ 0 → kA * w ≤ kRho * (P i).ang (P j)

/-- An ordered pair `(i, j)` is a *candidate* if `P_i` is central, `P_j` is deep, and their
center lines meet in a single point of `ρD`. -/
def IsCandidate (P : ι → Plank) (i j : ι) : Prop :=
  i ≠ j ∧ IsCentral (P i) ∧ IsDeep (P j) ∧ CrossIn (P i) (P j) kRho

/-- `N(P,Q)`: members making angle less than `2 ang(P,Q)` with `P` or with `Q`. -/
def nbhdFam (P : ι → Plank) (i j : ι) : Set ι :=
  {k | min ((P k).ang (P i)) ((P k).ang (P j)) < 2 * (P i).ang (P j)}

/-- A candidate pair is *removable* if `N(P,Q)` covers a `τ`-fraction of the hull. -/
def IsRemovable (P : ι → Plank) (i j : ι) : Prop :=
  IsCandidate P i j ∧
    ENNReal.ofReal kTau * volume (hull (P i) (P j)) ≤
      volume (hull (P i) (P j) ∩ ⋃ k ∈ nbhdFam P i j, (P k).carrier)

open Classical in
/-- The set of indices removed by a family of pairs. -/
def removedSet (pairs : Finset (ι × ι)) : Finset ι := pairs.biUnion fun p => {p.1, p.2}

/-- A pruning: a family of pairwise disjoint removable pairs. -/
structure IsPruning (P : ι → Plank) (pairs : Finset (ι × ι)) : Prop where
  removable : ∀ p ∈ pairs, IsRemovable P p.1 p.2
  disjoint : (pairs : Set (ι × ι)).PairwiseDisjoint fun p => ({p.1, p.2} : Set ι)

/-- A final pruning: no removable pair survives. -/
structure IsFinalPruning (P : ι → Plank) (pairs : Finset (ι × ι)) : Prop
    extends IsPruning P pairs where
  final : ∀ i j, i ∉ removedSet pairs → j ∉ removedSet pairs → ¬ IsRemovable P i j

/-- The final hole `H_f = int D \ ⋃_{surviving} P`. -/
def finalHole (P : ι → Plank) (pairs : Finset (ι × ι)) : Set Plane :=
  ball 0 1 \ ⋃ (i) (_ : i ∉ removedSet pairs), (P i).carrier

/-- A `δ`-dense disk: an open disk `B ⊆ D` with `∫_B (M - 1)₊ > δ |B|`. -/
def IsDenseDisk (P : ι → Plank) (δ : ℝ) (c : Plane) (t : ℝ) : Prop :=
  0 < t ∧ ball c t ⊆ unitDisk ∧
    ENNReal.ofReal δ * volume (ball c t) < ∫⁻ x in ball c t, ((countF P x : ℝ≥0∞) - 1)

/-- The dense region `U_δ`: the union of all `δ`-dense disks. -/
def denseRegion (P : ι → Plank) (δ : ℝ) : Set Plane :=
  ⋃ (c : Plane) (t : ℝ) (_ : IsDenseDisk P δ c t), ball c t

end Family

end Annulus

end
