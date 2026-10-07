module

public import Mathlib

/-!
# A one-dimensional covering lemma

Given finitely many points `u_i` on the line, there are disjoint intervals of total length
`≥ min (N w/(16κ), 2C/3)` such that every point of these intervals is either within `w/8` of
some `u_i`, or has at least `κ s / w` of the points within some distance `s ∈ [2w, 2C]`.
-/

@[expose] public section

open Set

noncomputable section

namespace Annulus

/-- The number of points `u_j`, `j ∈ T`, within distance `s` of `x`. -/
def nearCount {α : Type*} (T : Finset α) (u : α → ℝ) (x s : ℝ) : ℕ :=
  (T.filter fun j => |x - u j| ≤ s).card

lemma nearCount_mono {α : Type*} (T : Finset α) (u : α → ℝ) (x : ℝ) {s s' : ℝ} (h : s ≤ s') :
    nearCount T u x s ≤ nearCount T u x s' := by
  unfold nearCount
  exact Finset.card_le_card fun j hj => by
    simp only [Finset.mem_filter] at hj ⊢; exact ⟨hj.1, hj.2.trans h⟩

theorem one_dim_cover {α : Type*} {κ w C : ℝ} (hκ : 0 < κ) (hw : 0 < w) (hC : 2 * w ≤ C)
    (T : Finset α) (u : α → ℝ) :
    ∃ V : Finset α, ∃ r : α → ℝ, V ⊆ T ∧
      (↑V : Set α).PairwiseDisjoint (fun j => Icc (u j - r j) (u j + r j)) ∧
      (∀ j ∈ V, 0 < r j ∧ r j ≤ C) ∧
      (∀ j ∈ V, ∀ x ∈ Icc (u j - r j) (u j + r j),
        (∃ i ∈ T, |x - u i| ≤ w / 8) ∨
        ∃ s, 2 * w ≤ s ∧ s ≤ 2 * C ∧ κ * s / w ≤ (nearCount T u x s : ℝ)) ∧
      min (T.card * w / (16 * κ)) (2 * C / 3) ≤ ∑ j ∈ V, 2 * r j := by
  classical
  set n : α → ℝ → ℕ := fun i s => nearCount T u (u i) s with hn
  set D : α → Set ℝ := fun i => {s | 2 * w ≤ s ∧ s ≤ C ∧ 2 * κ * s / w ≤ (n i s : ℝ)}
  set r : α → ℝ := fun i => if (D i).Nonempty then sSup (D i) else w / 8
  have hDbdd : ∀ i, BddAbove (D i) := fun i => ⟨C, fun s hs => hs.2.1⟩
  -- properties of the radius
  have hr_mem : ∀ i, (D i).Nonempty → r i ∈ D i := by
    intro i hne
    have hri : r i = sSup (D i) := by simp only [r, if_pos hne]
    obtain ⟨s0, hs0⟩ := hne
    refine ⟨?_, ?_, ?_⟩
    · rw [hri]; exact hs0.1.trans (le_csSup (hDbdd i) hs0)
    · rw [hri]; exact csSup_le ⟨s0, hs0⟩ fun s hs => hs.2.1
    · by_contra hcon
      push_neg at hcon
      set ε := (2 * κ * r i / w - n i (r i)) * w / (2 * κ)
      have hε : 0 < ε := by
        simp only [ε]; apply div_pos (mul_pos (by linarith) hw) (by positivity)
      obtain ⟨s, hsD, hs⟩ := exists_lt_of_lt_csSup ⟨s0, hs0⟩
        (show sSup (D i) - ε < sSup (D i) by linarith)
      rw [← hri] at hs
      have hsr : s ≤ r i := by rw [hri]; exact le_csSup (hDbdd i) hsD
      have h1 : (n i s : ℝ) ≤ n i (r i) := by exact_mod_cast nearCount_mono T u (u i) hsr
      have h2 : 2 * κ * s / w ≤ n i s := hsD.2.2
      have h3 : 2 * κ * (r i - ε) / w < 2 * κ * s / w := by
        apply div_lt_div_of_pos_right _ hw; nlinarith
      have h4 : 2 * κ * (r i - ε) / w = n i (r i) := by
        simp only [ε]; field_simp; ring
      linarith
  have hr_max : ∀ i, (D i).Nonempty → ∀ s, r i < s → s ∉ D i := by
    intro i hne s hs hsD
    have hri : r i = sSup (D i) := by simp only [r, if_pos hne]
    have := le_csSup (hDbdd i) hsD
    linarith
  have hr_pos : ∀ i, 0 < r i := by
    intro i
    by_cases hne : (D i).Nonempty
    · have := (hr_mem i hne).1; linarith
    · simp only [r, if_neg hne]; positivity
  have hr_le : ∀ i, r i ≤ C := by
    intro i
    by_cases hne : (D i).Nonempty
    · exact (hr_mem i hne).2.1
    · simp only [r, if_neg hne]; linarith
  -- Vitali selection
  obtain ⟨U, hUT, hUdisj, hUcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun i => Icc (u i - r i) (u i + r i)) (↑T : Set α) r (3 / 2) (by norm_num)
    (fun i _ => (hr_pos i).le) C (fun i _ => hr_le i)
    (fun i _ => nonempty_Icc.2 (by linarith [hr_pos i]))
  set V := T.filter (· ∈ U)
  have hVU : (↑V : Set α) = U := by
    ext j; simp only [V, Finset.coe_filter, mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨hUT h, h⟩⟩
  refine ⟨V, r, Finset.filter_subset _ _, by rw [hVU]; exact hUdisj,
    fun j _ => ⟨hr_pos j, hr_le j⟩, ?_, ?_⟩
  · -- good points
    intro j _ x hx
    rw [mem_Icc] at hx
    by_cases hne : (D j).Nonempty
    · right
      have hrj := hr_mem j hne
      refine ⟨2 * r j, by linarith [hrj.1], by linarith [hrj.2.1], ?_⟩
      have hcard : n j (r j) ≤ nearCount T u x (2 * r j) := by
        simp only [n, nearCount]
        exact Finset.card_le_card fun i hi => by
          simp only [Finset.mem_filter] at hi ⊢
          refine ⟨hi.1, ?_⟩
          have : |x - u j| ≤ r j := by rw [abs_le]; constructor <;> linarith
          calc |x - u i| = |(x - u j) + (u j - u i)| := by ring_nf
            _ ≤ |x - u j| + |u j - u i| := abs_add_le _ _
            _ ≤ r j + r j := add_le_add this hi.2
            _ = 2 * r j := by ring
      have : (n j (r j) : ℝ) ≤ nearCount T u x (2 * r j) := by exact_mod_cast hcard
      have h2 := hrj.2.2
      calc κ * (2 * r j) / w = 2 * κ * r j / w := by ring
        _ ≤ _ := h2.trans this
    · left
      refine ⟨j, Finset.mem_of_mem_filter _ ‹_›, ?_⟩
      have : r j = w / 8 := by simp only [r, if_neg hne]
      rw [abs_le]; constructor <;> linarith
  · -- total length
    by_cases hbig : ∃ j ∈ V, C < 3 * r j
    · obtain ⟨j, hj, hjC⟩ := hbig
      calc min (T.card * w / (16 * κ)) (2 * C / 3) ≤ 2 * C / 3 := min_le_right _ _
        _ ≤ 2 * r j := by linarith
        _ ≤ ∑ j ∈ V, 2 * r j :=
            Finset.single_le_sum (f := fun j => 2 * r j) (fun i _ => by linarith [hr_pos i]) hj
    · push_neg at hbig
      refine (min_le_left _ _).trans ?_
      -- each selected interval captures few points
      have hcap : ∀ j ∈ V, (n j (3 * r j) : ℝ) ≤ 16 * κ * (2 * r j) / w := by
        intro j hj
        by_cases hne : (D j).Nonempty
        · have hrj := hr_mem j hne
          have hnot := hr_max j hne (3 * r j) (by linarith [hr_pos j])
          simp only [D, mem_setOf_eq, not_and, not_le] at hnot
          have := hnot (by linarith [hrj.1]) (hbig j hj)
          have h6 : 2 * κ * (3 * r j) / w ≤ 16 * κ * (2 * r j) / w := by
            apply div_le_div_of_nonneg_right _ hw.le; nlinarith [hr_pos j]
          linarith
        · have hr : r j = w / 8 := by simp only [r, if_neg hne]
          have h2w : 2 * w ∉ D j := fun h => hne ⟨_, h⟩
          simp only [D, mem_setOf_eq, not_and, not_le] at h2w
          have h1 := h2w le_rfl hC
          have h2 : (n j (3 * r j) : ℝ) ≤ n j (2 * w) := by
            exact_mod_cast nearCount_mono T u (u j) (by rw [hr]; linarith)
          rw [hr] at h2 ⊢
          have : 2 * κ * (2 * w) / w = 16 * κ * (2 * (w / 8)) / w := by ring
          linarith
      -- every point is captured by some selected interval
      have hcover : T ⊆ V.biUnion fun j => T.filter fun i => |u j - u i| ≤ 3 * r j := by
        intro i hi
        obtain ⟨j, hjU, ⟨y, hy1, hy2⟩, hij⟩ := hUcov i (Finset.mem_coe.2 hi)
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        refine ⟨j, Finset.mem_filter.2 ⟨Finset.mem_coe.1 (hUT hjU), hjU⟩, hi, ?_⟩
        rw [mem_Icc] at hy1 hy2
        rw [abs_le]; constructor <;> linarith [hr_pos i, hr_pos j]
      have hT : (T.card : ℝ) ≤ ∑ j ∈ V, (n j (3 * r j) : ℝ) := by
        have := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
        exact_mod_cast this
      have : (T.card : ℝ) ≤ 16 * κ / w * ∑ j ∈ V, 2 * r j := by
        refine hT.trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j hj => ?_
        exact le_of_le_of_eq (hcap j hj) (by ring)
      rw [div_le_iff₀ (by positivity)]
      rw [div_mul_eq_mul_div, le_div_iff₀ hw] at this
      linarith

end Annulus

end
