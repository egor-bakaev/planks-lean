module

public import RequestProject.Overlap.Hull

/-!
# Cells of the final hole, greedy selection, and auxiliary plane geometry

* The final hole of a family of surviving planks `S` is partitioned by sign patterns
  `A ⊆ S` into the convex open *cells* `cell P S A`.
* An abstract greedy (Vitali-type) selection of pairwise disjoint sets.
* Small facts on coordinates and on crossing points of center lines.
-/

@[expose] public section

open MeasureTheory Set Metric Real
open scoped ENNReal

noncomputable section

namespace Annulus

/-! ### Plane geometry -/

/-- Decomposition of an inner product in the frame `(n, Jn)`. -/
lemma inner_decomp {n : Plane} (hn : ‖n‖ = 1) (x q : Plane) :
    inner ℝ x q = inner ℝ x n * inner ℝ n q + inner ℝ x (J n) * inner ℝ (J n) q := by
  conv_lhs => rw [decomp_frame hn x]
  simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]

/-- In the frame `(n₀, J n₀)`, `⟪J a, b⟫` is a `2 × 2` determinant. -/
lemma inner_J_frame {n0 : Plane} (hn0 : ‖n0‖ = 1) (a b : Plane) :
    inner ℝ (J a) b =
      inner ℝ a n0 * inner ℝ b (J n0) - inner ℝ a (J n0) * inner ℝ b n0 := by
  have h := unit_coord hn0
  simp only [inner_eq_coord, J_apply_zero, J_apply_one]
  linear_combination (a 1 * b 0 - a 0 * b 1) * h

lemma abs_inner_le_one {a b : Plane} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : |inner ℝ a b| ≤ 1 := by
  have := abs_real_inner_le_norm a b; rwa [ha, hb, mul_one] at this

lemma abs_inner_le_norm_of_unit {a : Plane} (ha : ‖a‖ = 1) (x : Plane) :
    |inner ℝ x a| ≤ ‖x‖ := by
  have := abs_real_inner_le_norm x a; rwa [ha, mul_one] at this

namespace Plank

/-- A point close to two nonparallel center lines is close to their crossing point. -/
lemma norm_sub_crossPt_le {P Q : Plank} (h : P.ang Q ≠ 0) {x : Plane} {δ : ℝ}
    (hP : |inner ℝ x P.n - P.mid| ≤ δ) (hQ : |inner ℝ x Q.n - Q.mid| ≤ δ) :
    ‖x - P.crossPt Q‖ ≤ δ + 2 * δ / |inner ℝ (J P.n) Q.n| := by
  have hs := P.sin_ang_pos h
  set c := P.crossPt Q
  set d := x - c
  have hdP : inner ℝ d P.n = inner ℝ x P.n - P.mid := by
    rw [inner_sub_left, mem_centerLine.1 (crossPt_mem_left P Q)]
  have hdQ : inner ℝ d Q.n = inner ℝ x Q.n - Q.mid := by
    rw [inner_sub_left, mem_centerLine.1 (crossPt_mem_right h)]
  have hdec := inner_decomp P.norm_n d Q.n
  have hc : |inner ℝ P.n Q.n| ≤ 1 := P.abs_inner_n_le Q
  have h1 : |inner ℝ d (J P.n)| * |inner ℝ (J P.n) Q.n| ≤ 2 * δ := by
    rw [← abs_mul]
    have : inner ℝ d (J P.n) * inner ℝ (J P.n) Q.n =
        inner ℝ d Q.n - inner ℝ d P.n * inner ℝ P.n Q.n := by linarith
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, hdP, hdQ]
    have : |inner ℝ x P.n - P.mid| * |inner ℝ P.n Q.n| ≤ δ := by
      calc _ ≤ |inner ℝ x P.n - P.mid| * 1 := by gcongr
        _ ≤ δ := by linarith
    linarith
  have h2 : |inner ℝ d (J P.n)| ≤ 2 * δ / |inner ℝ (J P.n) Q.n| := by
    rw [le_div_iff₀ hs]; exact h1
  have h3 : ‖d‖ ≤ |inner ℝ d P.n| + |inner ℝ d (J P.n)| := by
    conv_lhs => rw [decomp_frame P.norm_n d]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, P.norm_n, norm_J, P.norm_n, mul_one, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs]
  rw [hdP] at h3
  linarith

end Plank

/-! ### Cells -/

variable {ι : Type*} [Fintype ι]

/-- The hole left by the planks with indices in `S`. -/
def holeS (P : ι → Plank) (S : Finset ι) : Set Plane := ball 0 1 \ ⋃ k ∈ S, (P k).carrier

/-- The cell with sign pattern `A`: points of `int D` below the planks in `A` and above the
other planks of `S`. -/
def cell (P : ι → Plank) (S A : Finset ι) : Set Plane :=
  {y | ‖y‖ < 1 ∧ ∀ k ∈ S, (k ∈ A → inner ℝ y (P k).n < (P k).a) ∧
    (k ∉ A → (P k).b < inner ℝ y (P k).n)}

omit [Fintype ι] in
lemma convex_cell (P : ι → Plank) (S A : Finset ι) : Convex ℝ (cell P S A) := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  refine ⟨?_, fun k hk => ⟨fun hkA => ?_, fun hkA => ?_⟩⟩
  · have := (convex_ball (0 : Plane) 1) (mem_ball_zero_iff.2 hx.1) (mem_ball_zero_iff.2 hy.1)
      ha.le hb.le hab
    exact mem_ball_zero_iff.1 this
  · have h1 := (hx.2 k hk).1 hkA
    have h2 := (hy.2 k hk).1 hkA
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    have := add_lt_add (mul_lt_mul_of_pos_left h1 ha) (mul_lt_mul_of_pos_left h2 hb)
    rw [← add_mul, hab, one_mul] at this
    exact this
  · have h1 := (hx.2 k hk).2 hkA
    have h2 := (hy.2 k hk).2 hkA
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    have := add_lt_add (mul_lt_mul_of_pos_left h1 ha) (mul_lt_mul_of_pos_left h2 hb)
    rw [← add_mul, hab, one_mul] at this
    exact this

omit [Fintype ι] in
lemma measurableSet_cell (P : ι → Plank) (S A : Finset ι) : MeasurableSet (cell P S A) := by
  have : cell P S A = {y : Plane | ‖y‖ < 1} ∩ ⋂ k ∈ S,
      {y | (k ∈ A → inner ℝ y (P k).n < (P k).a) ∧ (k ∉ A → (P k).b < inner ℝ y (P k).n)} := by
    ext y; simp [cell]
  rw [this]
  refine (measurableSet_lt (by fun_prop) measurable_const).inter
    (Finset.measurableSet_biInter _ fun k _ => ?_)
  have hm : Measurable fun y : Plane => inner ℝ y (P k).n :=
    (continuous_id.inner continuous_const).measurable
  by_cases hk : k ∈ A
  · simp only [hk, true_implies, not_true_eq_false, false_implies, and_true]
    exact measurableSet_lt hm measurable_const
  · simp only [hk, false_implies, not_false_eq_true, true_implies, true_and]
    exact measurableSet_lt measurable_const hm

omit [Fintype ι] in
lemma cell_subset_holeS (P : ι → Plank) (S A : Finset ι) : cell P S A ⊆ holeS P S := by
  intro y hy
  refine ⟨mem_ball_zero_iff.2 hy.1, ?_⟩
  simp only [mem_iUnion, not_exists]
  intro k hk hyk
  have hc := hyk
  simp only [Plank.carrier, mem_setOf_eq] at hc
  by_cases hkA : k ∈ A
  · have := (hy.2 k hk).1 hkA; linarith [hc.1]
  · have := (hy.2 k hk).2 hkA; linarith [hc.2]

omit [Fintype ι] in
lemma holeS_subset_cells (P : ι → Plank) (S : Finset ι) :
    holeS P S ⊆ ⋃ A ∈ S.powerset, cell P S A := by
  classical
  intro y hy
  obtain ⟨hy1, hy2⟩ := hy
  simp only [mem_iUnion, not_exists] at hy2
  simp only [mem_iUnion]
  refine ⟨S.filter fun k => inner ℝ y (P k).n < (P k).a, Finset.mem_powerset.2
    (Finset.filter_subset _ _), mem_ball_zero_iff.1 hy1, fun k hk => ⟨fun hkA => ?_, fun hkA => ?_⟩⟩
  · exact (Finset.mem_filter.1 hkA).2
  · have h1 : (P k).a ≤ inner ℝ y (P k).n := by
      by_contra h; push_neg at h; exact hkA (Finset.mem_filter.2 ⟨hk, h⟩)
    by_contra h2; push_neg at h2
    exact hy2 k hk ⟨h1, h2⟩

omit [Fintype ι] in
lemma cell_pairwiseDisjoint (P : ι → Plank) (S : Finset ι) :
    (↑S.powerset : Set (Finset ι)).PairwiseDisjoint (cell P S) := by
  intro A hA B hB hAB
  rw [Function.onFun, Set.disjoint_left]
  intro y hyA hyB
  simp only [Finset.coe_powerset, mem_preimage, mem_powerset_iff, Finset.coe_subset] at hA hB
  obtain ⟨k, hk⟩ : ∃ k, ¬(k ∈ A ↔ k ∈ B) := by
    by_contra h; push_neg at h; exact hAB (Finset.ext h)
  have hab := (P k).a_le_b
  by_cases hkA : k ∈ A
  · have hkB : k ∉ B := fun h => hk ⟨fun _ => h, fun _ => hkA⟩
    have h1 := (hyA.2 k (hA hkA)).1 hkA
    have h2 := (hyB.2 k (hA hkA)).2 hkB
    linarith
  · have hkB : k ∈ B := by
      by_contra h; exact hk ⟨fun h' => absurd h' hkA, fun h' => absurd h' h⟩
    have h1 := (hyA.2 k (hB hkB)).2 hkA
    have h2 := (hyB.2 k (hB hkB)).1 hkB
    linarith

/-! ### Greedy selection -/

/-- A greedy selection: pairwise disjoint members such that every member meets a selected
member of at least the same weight. -/
lemma greedy_select {α : Type*} (B : Finset α) (h : α → ℝ) (R : α → Set Plane) :
    ∃ V ⊆ B, (↑V : Set α).PairwiseDisjoint R ∧
      ∀ k ∈ B, ∃ j ∈ V, h k ≤ h j ∧ (j = k ∨ (R j ∩ R k).Nonempty) := by
  classical
  induction hn : B.card using Nat.strong_induction_on generalizing B with
  | _ n ih =>
  rcases B.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, subset_rfl, by simp, by simp⟩
  obtain ⟨j, hjB, hjmax⟩ := B.exists_max_image h hne
  set B' := (B.erase j).filter fun k => Disjoint (R k) (R j)
  have hcard : B'.card < n := by
    rw [← hn]
    calc B'.card ≤ (B.erase j).card := Finset.card_filter_le _ _
      _ < B.card := Finset.card_erase_lt_of_mem hjB
  obtain ⟨V', hV'B, hV'disj, hV'cov⟩ := ih _ hcard B' rfl
  refine ⟨insert j V', ?_, ?_, ?_⟩
  · intro k hk
    rcases Finset.mem_insert.1 hk with rfl | hk
    · exact hjB
    · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_filter _ (hV'B hk))
  · rw [Finset.coe_insert]
    refine hV'disj.insert fun k hk _ => ?_
    exact (Finset.mem_filter.1 (hV'B hk)).2.symm
  · intro k hk
    by_cases hkj : k = j
    · exact ⟨j, Finset.mem_insert_self _ _, by rw [hkj], Or.inl hkj.symm⟩
    by_cases hdisj : Disjoint (R k) (R j)
    · have hkB' : k ∈ B' := Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨hkj, hk⟩, hdisj⟩
      obtain ⟨j', hj', h1, h2⟩ := hV'cov k hkB'
      exact ⟨j', Finset.mem_insert_of_mem hj', h1, h2⟩
    · refine ⟨j, Finset.mem_insert_self _ _, hjmax k hk, Or.inr ?_⟩
      rw [Set.not_disjoint_iff_nonempty_inter] at hdisj
      rwa [Set.inter_comm]

end Annulus

end
