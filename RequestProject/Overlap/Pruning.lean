module

public import RequestProject.Overlap.Cone
public import RequestProject.Overlap.Needle
public import RequestProject.Overlap.Select
public import RequestProject.Overlap.DenseDisk

/-!
# Pruning amplifies the hole (Theorem 4.3)

Cells of the final hole are either *good* (much larger than their part in `rD`) or *bad*.
Bad cells lie in `B(0, 0.032 ρ)` (cone estimate) and are thin needles along the center line of
a central survivor with a candidate partner (needle lemma).  A greedy selection of pairwise
disjoint carrier bands, together with the two-line comparison, bounds the part of the bad
cells in `rD` by a small multiple of `(r/ρ) |H_f|`.
-/

@[expose] public section

open MeasureTheory Set Metric Real
open scoped ENNReal

noncomputable section

namespace Annulus

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- The carrier band of a maximal surviving candidate pair contains a definite amount of the
final hole. -/
theorem band_hole_mass (P : ι → Plank) {w : ℝ} (hw0 : 0 < w) (hw : EqualWidth P w)
    (hsep : AngleSep P w) {S : Finset ι} {k l : ι} (hcand : IsCandidate P k l)
    (hnr : ¬ IsRemovable P k l)
    (hmax : ∀ m ∈ S, IsCandidate P k m →
      |inner ℝ (J (P k).n) (P m).n| ≤ |inner ℝ (J (P k).n) (P l).n|) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      carrierBand (P k) σ (7 / 100 * kRho * |inner ℝ (J (P k).n) (P l).n|) ⊆ ball 0 1 ∧
      ENNReal.ofReal (83 / 1000 * kRho ^ 2 * |inner ℝ (J (P k).n) (P l).n|) ≤
        volume (carrierBand (P k) σ (7 / 100 * kRho * |inner ℝ (J (P k).n) (P l).n|) ∩
          holeS P S) := by
  obtain ⟨σ, hσ, hdiff, hball⟩ := carrier_band P hw0 hw hsep hcand hnr hmax
  refine ⟨σ, hσ, hball, ?_⟩
  set s := |inner ℝ (J (P k).n) (P l).n|
  set Bd := carrierBand (P k) σ (7 / 100 * kRho * s)
  have hρ := kRho_pos
  have hs : 0 ≤ s := abs_nonneg _
  have h1 := le_volume_carrierBand (P k) (h := 7 / 100 * kRho * s) hσ
  have h2 : volume Bd ≤ volume (Bd ∩ holeS P S) + volume (Bd \ holeS P S) :=
    measure_le_inter_add_diff _ _ _
  have h3 : ENNReal.ofReal (83 / 1000 * kRho ^ 2 * s) + ENNReal.ofReal (kTau * (8 * kRho ^ 2 * s))
      ≤ ENNReal.ofReal (6 / 5 * kRho * (7 / 100 * kRho * s)) := by
    rw [← ENNReal.ofReal_add (by positivity) (by norm_num [kTau]; positivity)]
    apply ENNReal.ofReal_le_ofReal
    norm_num [kTau]
    nlinarith
  have h4 : ENNReal.ofReal (83 / 1000 * kRho ^ 2 * s) + ENNReal.ofReal (kTau * (8 * kRho ^ 2 * s))
      ≤ volume (Bd ∩ holeS P S) + ENNReal.ofReal (kTau * (8 * kRho ^ 2 * s)) :=
    h3.trans (h1.trans (h2.trans (add_le_add_right hdiff _)))
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h4

omit [Fintype ι] in
/-- A maximal candidate partner exists as soon as some candidate partner exists. -/
lemma exists_max_partner (P : ι → Plank) {S : Finset ι} {k l0 : ι} (hl0 : l0 ∈ S)
    (hc : IsCandidate P k l0) :
    ∃ l ∈ S, IsCandidate P k l ∧ ∀ m ∈ S, IsCandidate P k m →
      |inner ℝ (J (P k).n) (P m).n| ≤ |inner ℝ (J (P k).n) (P l).n| := by
  classical
  obtain ⟨l, hl, hlmax⟩ := (S.filter (IsCandidate P k)).exists_max_image
    (fun m => |inner ℝ (J (P k).n) (P m).n|) ⟨l0, Finset.mem_filter.2 ⟨hl0, hc⟩⟩
  exact ⟨l, (Finset.mem_filter.1 hl).1, (Finset.mem_filter.1 hl).2,
    fun m hm hcm => hlmax m (Finset.mem_filter.2 ⟨hm, hcm⟩)⟩

omit [Fintype ι] in
/-- If the final hole is small, any two central survivors are almost parallel. -/
theorem central_pair_small (P : ι → Plank) {w : ℝ} (hw0 : 0 < w) (hw : EqualWidth P w)
    (hsep : AngleSep P w) {S : Finset ι} (hfinS : ∀ k ∈ S, ∀ l ∈ S, ¬ IsRemovable P k l)
    (hsmall : volume (holeS P S) < ENNReal.ofReal (kRho ^ 2 / 1000)) :
    ∀ k ∈ S, ∀ l ∈ S, IsCentral (P k) → IsCentral (P l) →
      |inner ℝ (J (P k).n) (P l).n| < 1 / 5 := by
  intro k hk l hl hck hcl
  have hρ := kRho_pos
  by_contra h
  push_neg at h
  have hs0 : 0 < |inner ℝ (J (P k).n) (P l).n| := by linarith
  have hang : (P k).ang (P l) ≠ 0 := (Plank.ang_ne_zero_iff _ _).2 (fun h0 => by
    rw [h0, abs_zero] at h; linarith)
  have hcand : IsCandidate P k l := by
    refine ⟨fun hkl => ?_, hck, ?_, hang, (P k).crossPt (P l), ?_, Plank.crossPt_mem_left _ _,
      Plank.crossPt_mem_right hang⟩
    · subst hkl; rw [inner_J_self, abs_zero] at h; linarith
    · unfold IsDeep; unfold IsCentral at hcl; linarith
    · have h1 := Plank.norm_crossPt_le hang
      unfold IsCentral at hck hcl
      have h2 : (|(P l).mid| + |(P k).mid|) / |inner ℝ (J (P k).n) (P l).n| ≤ 7 / 10 * kRho := by
        rw [div_le_iff₀ hs0]; nlinarith
      linarith
  obtain ⟨l', hl'S, hl'C, hl'max⟩ := exists_max_partner P hl hcand
  obtain ⟨σ, -, -, hmass⟩ := band_hole_mass P hw0 hw hsep hl'C (hfinS k hk l' hl'S) hl'max
  have hge := hl'max l hl hcand
  have h1 := (hmass.trans (measure_mono inter_subset_right)).trans_lt hsmall
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h1
  nlinarith

set_option maxHeartbeats 4000000 in
/-- Theorem 4.3: every final pruning amplifies the hole by the factor `ρ/(1000 r)`. -/
theorem pruning_hole (P : ι → Plank) {w r : ℝ} (hw0 : 0 < w) (hw : EqualWidth P w)
    (hr : 0 < r) (hrρ : r ≤ kRho / 2000) (hwr : w ≤ r / 100) (hsep : AngleSep P w)
    (hH : holeF P ⊆ closedBall 0 r) {pairs : Finset (ι × ι)}
    (hfin : IsFinalPruning P pairs) :
    ENNReal.ofReal (kRho / (1000 * r)) * volume (holeF P) ≤ volume (finalHole P pairs) := by
  classical
  have hρ := kRho_pos
  set L := kRho / (1000 * r) with hL_def
  have hL2 : 2 ≤ L := by rw [hL_def, le_div_iff₀ (by positivity)]; linarith
  have hLr : L * r = kRho / 1000 := by rw [hL_def]; field_simp
  set S := Finset.univ.filter fun k => k ∉ removedSet pairs with hS_def
  have hHf : finalHole P pairs = holeS P S := by
    ext x; simp [finalHole, holeS, S]
  rw [hHf]
  have hfinS : ∀ k ∈ S, ∀ l ∈ S, ¬ IsRemovable P k l := fun k hk l hl =>
    hfin.final k l (Finset.mem_filter.1 hk).2 (Finset.mem_filter.1 hl).2
  have hwρ : w ≤ kRho / 1000 := by linarith
  set Hf := holeS P S with hHf_def
  have hHfm : MeasurableSet Hf :=
    measurableSet_ball.diff (Finset.measurableSet_biUnion _ fun k _ => (P k).measurableSet_carrier)
  have hr1 : r < 1 := by have : kRho < 1 := by norm_num [kRho]
                         linarith
  have hH0 : holeF P ⊆ Hf ∩ closedBall 0 r := by
    intro x hx
    have hxr := hH hx
    refine ⟨⟨?_, ?_⟩, hxr⟩
    · rw [mem_ball_zero_iff]; have := mem_closedBall_zero_iff.1 hxr; linarith
    · have := hx.2
      simp only [mem_iUnion, not_exists] at this ⊢
      exact fun k _ => this k
  have hH0vol : volume (holeF P) ≤ ENNReal.ofReal (4 * r ^ 2) := by
    refine (measure_mono (hH0.trans inter_subset_right)).trans ?_
    rw [Measure.addHaar_closedBall_eq_addHaar_ball]; exact volume_ball_le_sq 0 r
  by_cases hbig : ENNReal.ofReal (L * (4 * r ^ 2)) ≤ volume Hf
  · calc ENNReal.ofReal L * volume (holeF P) ≤ ENNReal.ofReal L * ENNReal.ofReal (4 * r ^ 2) := by
          gcongr
      _ = ENNReal.ofReal (L * (4 * r ^ 2)) := (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ _ := hbig
  push_neg at hbig
  have hsmall : volume Hf < ENNReal.ofReal (kRho ^ 2 / 1000) := by
    refine hbig.trans_le (ENNReal.ofReal_le_ofReal ?_)
    have : L * (4 * r ^ 2) = 4 * (L * r) * r := by ring
    rw [this, hLr]; nlinarith
  have hpar := central_pair_small P hw0 hw hsep hfinS hsmall
  -- central survivors with a candidate partner, and their maximal partners
  set B := S.filter fun k => IsCentral (P k) ∧ ∃ l ∈ S, IsCandidate P k l with hB_def
  have hmaxex : ∀ k ∈ B, ∃ l ∈ S, IsCandidate P k l ∧ ∀ m ∈ S, IsCandidate P k m →
      |inner ℝ (J (P k).n) (P m).n| ≤ |inner ℝ (J (P k).n) (P l).n| := by
    intro k hk
    obtain ⟨-, -, l0, hl0S, hl0⟩ := Finset.mem_filter.1 hk
    exact exists_max_partner P hl0S hl0
  choose! lst hlstS hlstC hlstM using hmaxex
  set sst : ι → ℝ := fun k => |inner ℝ (J (P k).n) (P (lst k)).n| with hsst_def
  have hbandex : ∀ k ∈ B, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      carrierBand (P k) σ (7 / 100 * kRho * sst k) ⊆ ball 0 1 ∧
      ENNReal.ofReal (83 / 1000 * kRho ^ 2 * sst k) ≤
        volume (carrierBand (P k) σ (7 / 100 * kRho * sst k) ∩ Hf) := fun k hk =>
    band_hole_mass P hw0 hw hsep (hlstC k hk)
      (hfinS k (Finset.mem_filter.1 hk).1 _ (hlstS k hk)) (hlstM k hk)
  choose! σ hσ hσball hσmass using hbandex
  set band : ι → Set Plane := fun k => carrierBand (P k) (σ k) (7 / 100 * kRho * sst k)
    with hband_def
  obtain ⟨V, hVB, hVdisj, hVcov⟩ := greedy_select B sst band
  -- the reference direction
  obtain ⟨n0, hn0, hn0par⟩ : ∃ n0 : Plane, ‖n0‖ = 1 ∧
      ∀ k ∈ S, IsCentral (P k) → |inner ℝ (J n0) (P k).n| < 1 / 5 := by
    by_cases h : ∃ k0 ∈ S, IsCentral (P k0)
    · obtain ⟨k0, hk0, hc0⟩ := h
      exact ⟨(P k0).n, (P k0).norm_n, fun k hk hc => hpar k0 hk0 k hk hc0 hc⟩
    · push_neg at h
      exact ⟨EuclideanSpace.single 0 1, by simp, fun k hk hc => absurd hc (h k hk)⟩
  -- bad cells are covered by the enlarged strips of the selected planks
  set good : Finset ι → Prop := fun A =>
    ENNReal.ofReal (2 * L) * volume (cell P S A ∩ closedBall 0 r) ≤ volume (cell P S A)
    with hgood_def
  set strip : ι → Set Plane := fun j =>
    {x | |inner ℝ x (P j).n - (P j).mid| ≤ 6 / 5 * kRho * sst j} ∩ closedBall 0 r
    with hstrip_def
  have hbadcov : ∀ A ∈ S.powerset, ¬ good A →
      cell P S A ∩ closedBall 0 r ⊆ ⋃ j ∈ V, strip j := by
    intro A _ hbad x hx
    have hsub : cell P S A ⊆ closedBall 0 (32 / 1000 * kRho) := by
      intro v hv
      rw [mem_closedBall_zero_iff]
      by_contra hvn
      push_neg at hvn
      apply hbad
      apply cone_estimate (convex_cell P S A) hr (by linarith)
        ((measurableSet_cell P S A).inter measurableSet_closedBall) hv
      rw [mul_assoc, hLr]; linarith
    obtain ⟨k, hkS, l, hlS, hcand, hnd⟩ := needle_aux P hw0 hw hsep hwρ hr hrρ hn0 hn0par hx.1
      (mem_closedBall_zero_iff.1 hx.2) hsub
    have hkB : k ∈ B := Finset.mem_filter.2 ⟨hkS, hcand.2.1, l, hlS, hcand⟩
    have hkl : |inner ℝ (J (P k).n) (P l).n| ≤ sst k := hlstM k hkB l hlS hcand
    obtain ⟨j, hjV, hjk, hjor⟩ := hVcov k hkB
    have hjB := hVB hjV
    simp only [mem_iUnion]
    refine ⟨j, hjV, ?_, hx.2⟩
    have hxk : |inner ℝ x (P k).n - (P k).mid| ≤ 7 / 100 * kRho * sst k :=
      (hnd x hx.1).trans (by gcongr)
    rcases hjor with rfl | hmeet
    · show |inner ℝ x (P j).n - (P j).mid| ≤ 6 / 5 * kRho * sst j
      have : 0 ≤ sst j := abs_nonneg _
      nlinarith
    · refine strip_cover (hσ j hjB) (hσ k hkB) hcand.2.1 (abs_nonneg _) hjk hrρ
        (fun hang hcr => hlstM j hjB k hkS ⟨fun hjk' => ?_, (Finset.mem_filter.1 hjB).2.1,
          ?_, hang, (P j).crossPt (P k), hcr, Plank.crossPt_mem_left _ _,
          Plank.crossPt_mem_right hang⟩) hmeet (mem_closedBall_zero_iff.1 hx.2) hxk
      · subst hjk'
        exact ((Plank.ang_ne_zero_iff _ _).1 hang) (inner_J_self _)
      · have := hcand.2.1; unfold IsCentral at this; unfold IsDeep; linarith
  -- the hole in `rD` is covered by the cells
  have hcover : Hf ∩ closedBall 0 r ⊆ ⋃ A ∈ S.powerset, (cell P S A ∩ closedBall 0 r) := by
    rintro x ⟨hx, hxr⟩
    have := holeS_subset_cells P S hx
    simp only [mem_iUnion] at this ⊢
    obtain ⟨A, hA, hxA⟩ := this
    exact ⟨A, hA, hxA, hxr⟩
  set X : Finset ι → ℝ≥0∞ := fun A => volume (cell P S A ∩ closedBall 0 r) with hX_def
  have h1 : volume (holeF P) ≤ ∑ A ∈ S.powerset, X A :=
    (measure_mono hH0).trans ((measure_mono hcover).trans (measure_biUnion_finset_le _ _))
  rw [← Finset.sum_filter_add_sum_filter_not S.powerset good] at h1
  -- good cells
  have hgood : ENNReal.ofReal L * ∑ A ∈ S.powerset.filter good, X A ≤
      ENNReal.ofReal (1 / 2) * volume Hf := by
    have h2 : ENNReal.ofReal (2 * L) * ∑ A ∈ S.powerset.filter good, X A ≤ volume Hf := by
      rw [Finset.mul_sum]
      calc ∑ A ∈ S.powerset.filter good, ENNReal.ofReal (2 * L) * X A
          ≤ ∑ A ∈ S.powerset.filter good, volume (cell P S A) :=
            Finset.sum_le_sum fun A hA => (Finset.mem_filter.1 hA).2
        _ ≤ ∑ A ∈ S.powerset, volume (cell P S A) :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = volume (⋃ A ∈ S.powerset, cell P S A) :=
            (measure_biUnion_finset (cell_pairwiseDisjoint P S)
              fun A _ => measurableSet_cell P S A).symm
        _ ≤ volume Hf := measure_mono (iUnion₂_subset fun A _ => cell_subset_holeS P S A)
    calc ENNReal.ofReal L * ∑ A ∈ S.powerset.filter good, X A
        = ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (2 * L) *
            ∑ A ∈ S.powerset.filter good, X A) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]; congr 2; ring
      _ ≤ ENNReal.ofReal (1 / 2) * volume Hf := by gcongr
  -- bad cells
  have hbad : ∑ A ∈ S.powerset.filter (fun A => ¬ good A), X A ≤
      ∑ j ∈ V, ENNReal.ofReal (4 * r * (6 / 5 * kRho * sst j)) := by
    have hdisj : (↑(S.powerset.filter fun A => ¬ good A) : Set (Finset ι)).PairwiseDisjoint
        fun A => cell P S A ∩ closedBall 0 r :=
      ((cell_pairwiseDisjoint P S).subset
        (Finset.coe_subset.2 (Finset.filter_subset _ _))).mono fun A => inter_subset_left
    calc ∑ A ∈ S.powerset.filter (fun A => ¬ good A), X A
        = volume (⋃ A ∈ S.powerset.filter (fun A => ¬ good A), cell P S A ∩ closedBall 0 r) :=
          (measure_biUnion_finset hdisj fun A _ =>
            (measurableSet_cell P S A).inter measurableSet_closedBall).symm
      _ ≤ volume (⋃ j ∈ V, strip j) := measure_mono (iUnion₂_subset fun A hA =>
          hbadcov A (Finset.mem_filter.1 hA).1 (Finset.mem_filter.1 hA).2)
      _ ≤ ∑ j ∈ V, volume (strip j) := measure_biUnion_finset_le _ _
      _ ≤ _ := Finset.sum_le_sum fun j _ =>
          volume_strip_inter_ball_le (P j).norm_n _ _ 0 r
  -- selected carrier bands
  have hcar : ∑ j ∈ V, ENNReal.ofReal (83 / 1000 * kRho ^ 2 * sst j) ≤ volume Hf := by
    have hdisj : (↑V : Set ι).PairwiseDisjoint fun j => band j ∩ Hf :=
      hVdisj.mono fun j => inter_subset_left
    calc ∑ j ∈ V, ENNReal.ofReal (83 / 1000 * kRho ^ 2 * sst j)
        ≤ ∑ j ∈ V, volume (band j ∩ Hf) := Finset.sum_le_sum fun j hj => hσmass j (hVB hj)
      _ = volume (⋃ j ∈ V, band j ∩ Hf) :=
          (measure_biUnion_finset hdisj fun j _ =>
            (measurableSet_carrierBand _ _ _).inter hHfm).symm
      _ ≤ volume Hf := measure_mono (iUnion₂_subset fun j _ => inter_subset_right)
  have hbad2 : ENNReal.ofReal L * ∑ j ∈ V, ENNReal.ofReal (4 * r * (6 / 5 * kRho * sst j)) ≤
      ENNReal.ofReal (1 / 2) * ∑ j ∈ V, ENNReal.ofReal (83 / 1000 * kRho ^ 2 * sst j) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have hs : 0 ≤ sst j := abs_nonneg _
    have : L * (4 * r * (6 / 5 * kRho * sst j)) = 24 / 5 * (L * r) * kRho * sst j := by ring
    rw [this, hLr]
    have : 0 ≤ kRho ^ 2 * sst j := by positivity
    nlinarith
  calc ENNReal.ofReal L * volume (holeF P)
      ≤ ENNReal.ofReal L * (∑ A ∈ S.powerset.filter good, X A +
          ∑ A ∈ S.powerset.filter (fun A => ¬ good A), X A) := by gcongr
    _ = ENNReal.ofReal L * ∑ A ∈ S.powerset.filter good, X A +
          ENNReal.ofReal L * ∑ A ∈ S.powerset.filter (fun A => ¬ good A), X A := mul_add _ _ _
    _ ≤ ENNReal.ofReal (1 / 2) * volume Hf + ENNReal.ofReal (1 / 2) * volume Hf := by
        refine add_le_add hgood ?_
        calc ENNReal.ofReal L * ∑ A ∈ S.powerset.filter (fun A => ¬ good A), X A
            ≤ ENNReal.ofReal L * ∑ j ∈ V, ENNReal.ofReal (4 * r * (6 / 5 * kRho * sst j)) := by
              gcongr
          _ ≤ _ := hbad2
          _ ≤ ENNReal.ofReal (1 / 2) * volume Hf := by gcongr
    _ = volume Hf := by
        rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num

end Annulus

end
