module

public import RequestProject.Overlap.Dense
public import RequestProject.Overlap.Vitali
public import RequestProject.Overlap.Pruning

/-!
# The equal-width overlap estimate (Theorem 6.1)

Existence of final prunings, the counting argument, and the combination of the pruning
theorem, the price of removable pairs and the Vitali estimate for the dense region.
-/

@[expose] public section

open MeasureTheory Set Metric Real
open scoped ENNReal

noncomputable section

namespace Annulus

variable {ι : Type*} [Fintype ι]

/-- A plank meets the unit disk in area at most `2 w(P)`. -/
lemma volume_carrier_inter_unitDisk_le (P : Plank) :
    volume (P.carrier ∩ unitDisk) ≤ ENNReal.ofReal (2 * P.width) := by
  rw [P.carrier_eq, unitDisk]
  refine (volume_strip_inter_ball_le P.norm_n P.mid (P.width / 2) 0 1).trans ?_
  apply ENNReal.ofReal_le_ofReal; linarith

omit [Fintype ι] in
open Classical in
lemma mem_removedSet {pairs : Finset (ι × ι)} {k : ι} :
    k ∈ removedSet pairs ↔ ∃ p ∈ pairs, k = p.1 ∨ k = p.2 := by
  simp [removedSet, Finset.mem_biUnion]

open Classical in
/-- Every family has a final pruning (greedy deletion). -/
theorem exists_finalPruning (P : ι → Plank) : ∃ pairs, IsFinalPruning P pairs := by
  suffices h : ∀ n : ℕ, ∀ pairs : Finset (ι × ι), IsPruning P pairs →
      (Finset.univ.filter fun k => k ∉ removedSet pairs).card ≤ n →
        ∃ pairs', IsFinalPruning P pairs' by
    exact h _ ∅ ⟨by simp, by simp⟩ le_rfl
  intro n
  induction n with
  | zero =>
    intro pairs hp hcard
    refine ⟨pairs, hp, fun i j hi _ _ => ?_⟩
    have : i ∈ Finset.univ.filter fun k => k ∉ removedSet pairs := by simp [hi]
    rw [Nat.le_zero, Finset.card_eq_zero] at hcard
    simp [hcard] at this
  | succ n ih =>
    intro pairs hp hcard
    by_cases hex : ∃ i j, i ∉ removedSet pairs ∧ j ∉ removedSet pairs ∧ IsRemovable P i j
    · obtain ⟨i, j, hi, hj, hr⟩ := hex
      apply ih (insert (i, j) pairs)
      · refine ⟨?_, ?_⟩
        · intro p hp'
          rw [Finset.mem_insert] at hp'
          rcases hp' with rfl | hp'
          · exact hr
          · exact hp.removable p hp'
        · rw [Finset.coe_insert]
          refine hp.disjoint.insert fun q hq _ => ?_
          rw [Set.disjoint_left]
          intro k hk1 hk2
          have hkq : k ∈ removedSet pairs := mem_removedSet.2 ⟨q, hq, by simpa using hk2⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk1
          rcases hk1 with rfl | rfl
          · exact hi hkq
          · exact hj hkq
      · have hsub : (Finset.univ.filter fun k => k ∉ removedSet (insert (i, j) pairs)) ⊆
            (Finset.univ.filter fun k => k ∉ removedSet pairs).erase i := by
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro rfl
            exact hk (mem_removedSet.2 ⟨(k, j), Finset.mem_insert_self _ _, Or.inl rfl⟩)
          · intro hk'
            obtain ⟨p, hp', hkp⟩ := mem_removedSet.1 hk'
            exact hk (mem_removedSet.2 ⟨p, Finset.mem_insert_of_mem hp', hkp⟩)
        have hmem : i ∈ Finset.univ.filter fun k => k ∉ removedSet pairs := by simp [hi]
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hmem] at this
        omega
    · push_neg at hex
      exact ⟨pairs, hp, fun i j hi hj => hex i j hi hj⟩

omit [Fintype ι] in
open Classical in
lemma card_removedSet_le (pairs : Finset (ι × ι)) :
    (removedSet pairs).card ≤ 2 * pairs.card := by
  unfold removedSet
  refine Finset.card_biUnion_le.trans ?_
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun p _ => Finset.card_le_two

open Classical in
lemma finalHole_subset (P : ι → Plank) (pairs : Finset (ι × ι)) :
    finalHole P pairs ⊆ holeF P ∪ ⋃ k ∈ removedSet pairs, ((P k).carrier ∩ unitDisk) := by
  intro x hx
  simp only [finalHole, mem_diff, mem_iUnion, not_exists] at hx
  by_cases h : ∃ k, x ∈ (P k).carrier
  · obtain ⟨k, hk⟩ := h
    right
    have hkr : k ∈ removedSet pairs := by
      by_contra hc; exact hx.2 k hc hk
    simp only [mem_iUnion]
    exact ⟨k, hkr, hk, ball_subset_closedBall hx.1⟩
  · left
    push_neg at h
    exact ⟨ball_subset_closedBall hx.1, by simpa using h⟩

open Classical in
/-- Deleting the planks of `m` pairs enlarges the hole by at most `4 w m`. -/
lemma volume_finalHole_le (P : ι → Plank) {w : ℝ} (hw0 : 0 ≤ w) (hw : EqualWidth P w)
    (pairs : Finset (ι × ι)) :
    volume (finalHole P pairs) ≤ volume (holeF P) + ENNReal.ofReal (4 * w * pairs.card) := by
  refine (measure_mono (finalHole_subset P pairs)).trans ((measure_union_le _ _).trans ?_)
  gcongr
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ k ∈ removedSet pairs, volume ((P k).carrier ∩ unitDisk)
      ≤ ∑ _k ∈ removedSet pairs, ENNReal.ofReal (2 * w) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [← hw k]; exact volume_carrier_inter_unitDisk_le _
    _ = ENNReal.ofReal ((removedSet pairs).card * (2 * w)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (4 * w * pairs.card) := by
        apply ENNReal.ofReal_le_ofReal
        have := card_removedSet_le pairs
        have h' : ((removedSet pairs).card : ℝ) ≤ 2 * pairs.card := by exact_mod_cast this
        nlinarith

open Classical in
/-- The dense parts of the removed pairs have total area at most `|U_δ| + I(𝒫)`. -/
lemma sum_volume_dense_le (P : ι → Plank) {pairs : Finset (ι × ι)} (hp : IsPruning P pairs)
    (δ : ℝ) :
    ∑ p ∈ pairs, volume (denseRegion P δ ∩ ((P p.1).carrier ∪ (P p.2).carrier) ∩
        closedBall 0 (5 * kRho)) ≤ volume (denseRegion P δ) + excessF P := by
  set U := denseRegion P δ
  set S : ι × ι → Set Plane := fun p =>
    U ∩ ((P p.1).carrier ∪ (P p.2).carrier) ∩ closedBall 0 (5 * kRho) with hS
  have hSm : ∀ p, MeasurableSet (S p) := fun p =>
    (((isOpen_denseRegion P δ).measurableSet.inter
      ((P p.1).measurableSet_carrier.union (P p.2).measurableSet_carrier)).inter
      measurableSet_closedBall)
  have hUm : MeasurableSet U := (isOpen_denseRegion P δ).measurableSet
  -- pointwise bound
  have hpt : ∀ x, ∑ p ∈ pairs, (S p).indicator (1 : Plane → ℝ≥0∞) x ≤
      U.indicator (fun x => (countF P x : ℝ≥0∞)) x := by
    intro x
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx]
      have h1 : ∀ p ∈ pairs, (S p).indicator (1 : Plane → ℝ≥0∞) x ≤
          (({p.1, p.2} : Finset ι).filter fun k => x ∈ (P k).carrier).card := by
        intro p _
        by_cases hxp : x ∈ S p
        · rw [Set.indicator_of_mem hxp, Pi.one_apply]
          have hx' : x ∈ (P p.1).carrier ∪ (P p.2).carrier := hxp.1.2
          have : 0 < (({p.1, p.2} : Finset ι).filter fun k => x ∈ (P k).carrier).card := by
            rw [Finset.card_pos]
            rcases hx' with h | h
            · exact ⟨p.1, by simp [h]⟩
            · exact ⟨p.2, by simp [h]⟩
          exact_mod_cast this
        · rw [Set.indicator_of_notMem hxp]; exact zero_le
      refine (Finset.sum_le_sum h1).trans ?_
      rw [← Nat.cast_sum, ← Finset.card_biUnion]
      · unfold countF
        exact_mod_cast Finset.card_le_card (fun k hk => by
          simp only [Finset.mem_biUnion, Finset.mem_filter] at hk
          obtain ⟨_, _, _, hk⟩ := hk
          simp [hk])
      · intro p hp' q hq' hpq
        have hd := hp.disjoint (Finset.mem_coe.2 hp') (Finset.mem_coe.2 hq') hpq
        simp only [Function.onFun] at hd ⊢
        rw [Finset.disjoint_left]
        intro k hk1 hk2
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hk1 hk2
        exact Set.disjoint_left.1 hd (show k ∈ ({p.1, p.2} : Set ι) by
          rcases hk1.1 with h | h <;> simp [h]) (show k ∈ ({q.1, q.2} : Set ι) by
          rcases hk2.1 with h | h <;> simp [h])
    · rw [Set.indicator_of_notMem hx]
      refine le_of_eq (Finset.sum_eq_zero fun p _ => ?_)
      exact Set.indicator_of_notMem (fun h => hx h.1.1) _
  calc ∑ p ∈ pairs, volume (S p)
      = ∑ p ∈ pairs, ∫⁻ x, (S p).indicator 1 x := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [lintegral_indicator_one (hSm p)]
    _ = ∫⁻ x, ∑ p ∈ pairs, (S p).indicator 1 x := by
        rw [lintegral_finset_sum]
        intro p _
        exact measurable_one.indicator (hSm p)
    _ ≤ ∫⁻ x, U.indicator (fun x => (countF P x : ℝ≥0∞)) x := lintegral_mono hpt
    _ = ∫⁻ x in U, (countF P x : ℝ≥0∞) := lintegral_indicator hUm _
    _ ≤ ∫⁻ x in U, (1 + ((countF P x : ℝ≥0∞) - 1)) := by
        refine lintegral_mono fun x => ?_
        rw [add_comm]; exact le_tsub_add
    _ = volume U + ∫⁻ x in U, ((countF P x : ℝ≥0∞) - 1) := by
        rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul]
    _ ≤ volume U + excessF P := by
        gcongr
        exact lintegral_mono_set (denseRegion_subset_unitDisk P δ)

/-- The constant of the equal-width overlap estimate. -/
def cEq : ℝ := kGamma * kRho ^ 2 / (8000 * (25 / kDelta + 1))

lemma cEq_pos : 0 < cEq := by norm_num [cEq, kGamma, kRho, kDelta]

/-- Theorem 6.1 (equal-width overlap estimate). -/
theorem equalWidth_overlap (P : ι → Plank) {w r : ℝ} (hw0 : 0 < w) (hw : EqualWidth P w)
    (hr : 0 < r) (hrρ : r ≤ kRho / 2000) (hwr : w ≤ r / 100) (hsep : AngleSep P w)
    (hH : holeF P ⊆ closedBall 0 r) :
    ENNReal.ofReal (cEq / r) * volume (holeF P) ≤ excessF P := by
  classical
  obtain ⟨pairs, hfin⟩ := exists_finalPruning P
  set m := pairs.card
  set U := denseRegion P kDelta
  have hprune := pruning_hole P hw0 hw hr hrρ hwr hsep hH hfin
  have hcount := volume_finalHole_le P hw0.le hw pairs
  have hρ0 : 0 < kRho := kRho_pos
  have hγ0 : 0 < kGamma := by norm_num [kGamma]
  have hδ : (0 : ℝ) < kDelta := by norm_num [kDelta]
  have hwρ : w ≤ kRho / 100 := by
    have : r / 100 ≤ kRho / 100 := by
      have : r ≤ kRho := by have := kRho_pos; linarith
      linarith
    linarith
  have hpay : ∀ p ∈ pairs, ENNReal.ofReal (kGamma * kRho * w) ≤
      volume (U ∩ ((P p.1).carrier ∪ (P p.2).carrier) ∩ closedBall 0 (5 * kRho)) := by
    intro p hp
    have hrem := hfin.removable p hp
    exact removable_pays P hw0 hwρ hw hrem (hsep _ _ hrem.1.2.2.2.1)
  have hsum := sum_volume_dense_le P hfin.toIsPruning kDelta
  have hvit := volume_denseRegion_le P kDelta
  -- the pay bound summed
  have hm : ENNReal.ofReal (m * (kGamma * kRho * w)) ≤ volume U + excessF P := by
    refine le_trans ?_ hsum
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ← nsmul_eq_mul,
      ← Finset.sum_const]
    exact Finset.sum_le_sum hpay
  by_cases hI : excessF P = ∞
  · rw [hI]; exact le_top
  -- finiteness
  have hV0 : volume (holeF P) ≠ ∞ :=
    ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : Plane)) (r := r)).ne
      (measure_mono hH)
  have hU : volume U ≠ ∞ := by
    intro hU
    rw [hU, ENNReal.mul_top (by simpa using hδ)] at hvit
    exact hI (by
      rcases eq_top_or_lt_top (excessF P) with h | h
      · exact h
      · exfalso; exact absurd hvit (not_le.2 (ENNReal.mul_lt_top (by simp) h)))
  have hVf : volume (finalHole P pairs) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hV0, ENNReal.ofReal_ne_top⟩) hcount
  -- pass to real numbers
  set v0 := (volume (holeF P)).toReal
  set vf := (volume (finalHole P pairs)).toReal
  set I := (excessF P).toReal
  set u := (volume U).toReal
  have hv0 : 0 ≤ v0 := ENNReal.toReal_nonneg
  have hI0 : 0 ≤ I := ENNReal.toReal_nonneg
  have hu0 : 0 ≤ u := ENNReal.toReal_nonneg
  have e1 : kRho / (1000 * r) * v0 ≤ vf := by
    have := ENNReal.toReal_mono hVf hprune
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have e2 : vf ≤ v0 + 4 * w * m := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hV0, ENNReal.ofReal_ne_top⟩) hcount
    rwa [ENNReal.toReal_add hV0 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at this
  have e3 : m * (kGamma * kRho * w) ≤ u + I := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hU, hI⟩) hm
    rwa [ENNReal.toReal_add hU hI, ENNReal.toReal_ofReal (by positivity)] at this
  have e4 : kDelta * u ≤ 25 * I := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hI) hvit
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le] at this
  -- conclude
  rw [← ENNReal.ofReal_toReal hI, ← ENNReal.ofReal_toReal hV0, ← ENNReal.ofReal_mul
    (by have := cEq_pos; positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hlam : 2 ≤ kRho / (1000 * r) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have h5 : kRho / (1000 * r) * v0 ≤ 8 * (w * m) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hlam) hv0]
  have h7 : kRho * v0 ≤ 8000 * r * (w * m) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h5
    linarith
  have h8 : kGamma * kRho * (w * m) ≤ (25 / kDelta + 1) * I := by
    have hu : u ≤ 25 / kDelta * I := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]; linarith
    nlinarith
  have key : kGamma * kRho ^ 2 * v0 ≤ I * (8000 * (25 / kDelta + 1) * r) := by
    calc kGamma * kRho ^ 2 * v0 = kGamma * kRho * (kRho * v0) := by ring
      _ ≤ kGamma * kRho * (8000 * r * (w * m)) := by gcongr
      _ = 8000 * r * (kGamma * kRho * (w * m)) := by ring
      _ ≤ 8000 * r * ((25 / kDelta + 1) * I) := by gcongr
      _ = _ := by ring
  unfold cEq
  rw [div_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith

end Annulus

end
