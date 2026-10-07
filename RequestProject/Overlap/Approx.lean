module

public import RequestProject.Overlap.EqualWidth

/-!
# Equal-width approximation and the quantitative overlap theorem

Each plank is enlarged symmetrically to a width that is a multiple of `w` and cut into
pieces of width `w` (Lemma 3.1).  The hole and the excess change by at most `O(N w)`, and
letting `w → 0` in the equal-width estimate gives Theorem 2.1.
-/

@[expose] public section

open MeasureTheory Set Metric Real
open scoped ENNReal

noncomputable section

namespace Annulus

/-! ### Lines are null -/

lemma volume_line (n : Plane) (hn : ‖n‖ = 1) (c : ℝ) : volume {x : Plane | inner ℝ x n = c} = 0 := by
  have h : {x : Plane | inner ℝ x n = c} = ⋃ m : ℕ, ({x : Plane | |inner ℝ x n - c| ≤ 0} ∩
      closedBall 0 m) := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
    constructor
    · intro hx
      obtain ⟨m, hm⟩ := exists_nat_ge ‖x‖
      exact ⟨m, by simp [hx], hm⟩
    · rintro ⟨m, hx, _⟩
      have := abs_nonneg (inner ℝ x n - c)
      have h0 : |inner ℝ x n - c| = 0 := le_antisymm hx this
      rw [abs_eq_zero, sub_eq_zero] at h0
      exact h0
  rw [h]
  refine measure_iUnion_null fun m => ?_
  refine le_antisymm ((volume_strip_inter_ball_le hn c 0 0 m).trans ?_) zero_le
  simp

/-! ### Pieces -/

/-- The number of pieces `k = ⌊w(Q)/w⌋ + 1`. -/
def nPieces (Q : Plank) (w : ℝ) : ℕ := ⌊Q.width / w⌋₊ + 1

/-- The `j`-th piece of width `w` of the enlarged plank. -/
def piece (Q : Plank) {w : ℝ} (hw : 0 < w) (j : ℕ) : Plank where
  n := Q.n
  norm_n := Q.norm_n
  a := Q.mid - nPieces Q w * w / 2 + j * w
  b := Q.mid - nPieces Q w * w / 2 + j * w + w
  a_le_b := by linarith

/-- The enlarged plank `{x : |⟨x,n⟩ - mid| ≤ k w / 2}`. -/
def enlarged (Q : Plank) (w : ℝ) : Set Plane := {x | |inner ℝ x Q.n - Q.mid| ≤ nPieces Q w * w / 2}

lemma piece_width (Q : Plank) {w : ℝ} (hw : 0 < w) (j : ℕ) : (piece Q hw j).width = w := by
  simp [piece, Plank.width]

lemma width_lt_nPieces (Q : Plank) {w : ℝ} (hw : 0 < w) : Q.width < nPieces Q w * w := by
  have := Nat.lt_floor_add_one (Q.width / w)
  rw [div_lt_iff₀ hw] at this
  unfold nPieces; push_cast; linarith

lemma nPieces_le (Q : Plank) {w : ℝ} (hw : 0 < w) : nPieces Q w * w ≤ Q.width + w := by
  have := Nat.floor_le (div_nonneg Q.width_nonneg hw.le)
  unfold nPieces; push_cast
  rw [le_div_iff₀ hw] at this
  linarith

lemma carrier_subset_enlarged (Q : Plank) {w : ℝ} (hw : 0 < w) :
    Q.carrier ⊆ enlarged Q w := by
  intro x hx
  rw [Q.mem_carrier_iff] at hx
  have := width_lt_nPieces Q hw
  simp only [enlarged, mem_setOf_eq]
  linarith

lemma piece_subset_enlarged (Q : Plank) {w : ℝ} (hw : 0 < w) {j : ℕ} (hj : j < nPieces Q w) :
    (piece Q hw j).carrier ⊆ enlarged Q w := by
  intro x hx
  simp only [Plank.carrier, piece, mem_setOf_eq] at hx
  simp only [enlarged, mem_setOf_eq, abs_le]
  have hj' : (j : ℝ) + 1 ≤ nPieces Q w := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := by positivity
  constructor <;> nlinarith

lemma enlarged_subset_pieces (Q : Plank) {w : ℝ} (hw : 0 < w) {x : Plane}
    (hx : x ∈ enlarged Q w) : ∃ j < nPieces Q w, x ∈ (piece Q hw j).carrier := by
  simp only [enlarged, mem_setOf_eq, abs_le] at hx
  set k := nPieces Q w
  set t := inner ℝ x Q.n - (Q.mid - k * w / 2)
  have ht0 : 0 ≤ t := by simp only [t]; linarith
  have htk : t ≤ k * w := by simp only [t]; linarith
  have hk : 1 ≤ k := Nat.le_add_left 1 _
  have htdef : t = inner ℝ x Q.n - (Q.mid - k * w / 2) := rfl
  refine ⟨min ⌊t / w⌋₊ (k - 1), by omega, ?_⟩
  simp only [Plank.carrier, piece, mem_setOf_eq]
  change _ ≤ _ ∧ _ ≤ Q.mid - (k : ℝ) * w / 2 + _ * w + w
  rw [show Q.mid - ((nPieces Q w : ℕ) : ℝ) * w / 2 = Q.mid - (k : ℝ) * w / 2 from rfl]
  rcases le_total ⌊t / w⌋₊ (k - 1) with h | h
  · rw [min_eq_left h]
    have h1 := Nat.floor_le (div_nonneg ht0 hw.le)
    have h2 := Nat.lt_floor_add_one (t / w)
    rw [le_div_iff₀ hw] at h1
    rw [div_lt_iff₀ hw] at h2
    constructor <;> nlinarith
  · rw [min_eq_right h]
    have h1 := Nat.floor_le (div_nonneg ht0 hw.le)
    have hk1 : ((k - 1 : ℕ) : ℝ) = k - 1 := by rw [Nat.cast_sub hk]; simp
    rw [hk1]
    have : ((k - 1 : ℕ) : ℝ) ≤ ⌊t / w⌋₊ := by exact_mod_cast h
    rw [hk1] at this
    rw [le_div_iff₀ hw] at h1
    constructor <;> nlinarith

/-- Off the boundary lines, a point lies in at most one piece. -/
lemma piece_unique (Q : Plank) {w : ℝ} (hw : 0 < w) {x : Plane}
    (hx : ∀ j : ℕ, inner ℝ x Q.n ≠ Q.mid - nPieces Q w * w / 2 + j * w) {j j' : ℕ}
    (hj : x ∈ (piece Q hw j).carrier) (hj' : x ∈ (piece Q hw j').carrier) : j = j' := by
  simp only [Plank.carrier, piece, mem_setOf_eq] at hj hj'
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have h' : (j : ℝ) + 1 ≤ j' := by exact_mod_cast h
    have : inner ℝ x Q.n = Q.mid - nPieces Q w * w / 2 + (j + 1 : ℕ) * w := by
      push_cast; nlinarith
    exact hx _ this
  · have h' : (j' : ℝ) + 1 ≤ j := by exact_mod_cast h
    have : inner ℝ x Q.n = Q.mid - nPieces Q w * w / 2 + (j' + 1 : ℕ) * w := by
      push_cast; nlinarith
    exact hx _ this

/-- The extra region `Q' \ Q` meets the unit disk in area at most `2w`. -/
lemma volume_extra_le (Q : Plank) {w : ℝ} (hw : 0 < w) :
    volume ((enlarged Q w \ Q.carrier) ∩ unitDisk) ≤ ENNReal.ofReal (2 * w) := by
  set k := nPieces Q w
  have hk1 := width_lt_nPieces Q hw
  have hk2 := nPieces_le Q hw
  set t := (k * w - Q.width) / 4
  have hsub : (enlarged Q w \ Q.carrier) ∩ unitDisk ⊆
      ({x | |inner ℝ x Q.n - (Q.mid + Q.width / 2 + t)| ≤ t} ∩ closedBall 0 1) ∪
      ({x | |inner ℝ x Q.n - (Q.mid - Q.width / 2 - t)| ≤ t} ∩ closedBall 0 1) := by
    rintro x ⟨⟨hx1, hx2⟩, hx3⟩
    simp only [enlarged, mem_setOf_eq, abs_le] at hx1
    rw [Q.mem_carrier_iff, abs_le, not_and_or] at hx2
    simp only [mem_union, mem_inter_iff, mem_setOf_eq, abs_le]
    rcases hx2 with h | h
    · right; refine ⟨⟨?_, ?_⟩, hx3⟩ <;> simp only [t] <;> linarith
    · left; refine ⟨⟨?_, ?_⟩, hx3⟩ <;> simp only [t] <;> linarith
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (volume_strip_inter_ball_le Q.norm_n _ t 0 1)
    (volume_strip_inter_ball_le Q.norm_n _ t 0 1)).trans ?_
  rw [← ENNReal.ofReal_add (by simp only [t]; linarith) (by simp only [t]; linarith)]
  apply ENNReal.ofReal_le_ofReal
  simp only [t]; linarith

/-! ### The equal-width family -/

section Family

variable {ι : Type*} [Fintype ι]

/-- The equal-width family of pieces. -/
def pieceFam (P : ι → Plank) {w : ℝ} (hw : 0 < w) :
    (Σ i : ι, Fin (nPieces (P i) w)) → Plank :=
  fun p => piece (P p.1) hw p.2

omit [Fintype ι] in
lemma pieceFam_equalWidth (P : ι → Plank) {w : ℝ} (hw : 0 < w) :
    EqualWidth (pieceFam P hw) w := fun _ => piece_width _ hw _

omit [Fintype ι] in
lemma holeF_pieceFam_subset (P : ι → Plank) {w : ℝ} (hw : 0 < w) :
    holeF (pieceFam P hw) ⊆ holeF P := by
  rintro x ⟨hxD, hx⟩
  refine ⟨hxD, fun hx' => hx ?_⟩
  simp only [mem_iUnion] at hx' ⊢
  obtain ⟨i, hi⟩ := hx'
  obtain ⟨j, hj, hxj⟩ := enlarged_subset_pieces (P i) hw (carrier_subset_enlarged _ hw hi)
  exact ⟨⟨i, ⟨j, hj⟩⟩, hxj⟩

omit [Fintype ι] in
lemma holeF_subset_pieceFam (P : ι → Plank) {w : ℝ} (hw : 0 < w) :
    holeF P ⊆ holeF (pieceFam P hw) ∪ ⋃ i, ((enlarged (P i) w \ (P i).carrier) ∩ unitDisk) := by
  rintro x ⟨hxD, hx⟩
  by_cases h : x ∈ holeF (pieceFam P hw)
  · exact Or.inl h
  · right
    simp only [holeF, mem_diff, not_and, not_not, mem_iUnion] at h hx
    obtain ⟨p, hp⟩ := h hxD
    exact mem_iUnion.2 ⟨p.1, ⟨piece_subset_enlarged _ hw p.2.2 hp, fun h' => hx ⟨p.1, h'⟩⟩, hxD⟩

lemma volume_holeF_le_pieceFam (P : ι → Plank) {w : ℝ} (hw : 0 < w) :
    volume (holeF P) ≤ volume (holeF (pieceFam P hw)) +
      ENNReal.ofReal (Fintype.card ι * (2 * w)) := by
  refine (measure_mono (holeF_subset_pieceFam P hw)).trans ((measure_union_le _ _).trans ?_)
  gcongr
  refine (measure_iUnion_fintype_le _ _).trans ?_
  calc ∑ i, volume ((enlarged (P i) w \ (P i).carrier) ∩ unitDisk)
      ≤ ∑ _i : ι, ENNReal.ofReal (2 * w) := Finset.sum_le_sum fun i _ => volume_extra_le _ hw
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]

/-- Off the boundary lines, the counting function of the pieces is bounded by the counting
function of the original family plus the indicators of the extra regions. -/
lemma countF_pieceFam_le (P : ι → Plank) {w : ℝ} (hw : 0 < w) {x : Plane}
    (hx : ∀ i, ∀ j : ℕ, inner ℝ x (P i).n ≠ (P i).mid - nPieces (P i) w * w / 2 + j * w) :
    (countF (pieceFam P hw) x : ℝ≥0∞) ≤
      countF P x + ∑ i, (enlarged (P i) w \ (P i).carrier).indicator 1 x := by
  rw [countF_eq_sum, countF_eq_sum, ← Finset.sum_add_distrib]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_le_sum fun i _ => ?_
  -- at most one piece of `P i` contains `x`
  have hle1 : ∑ j : Fin (nPieces (P i) w), (pieceFam P hw ⟨i, j⟩).carrier.indicator
      (1 : Plane → ℝ≥0∞) x ≤ 1 := by
    classical
    rw [Finset.sum_indicator_eq_sum_filter]
    simp only [Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (Finset.univ.filter fun j : Fin (nPieces (P i) w) =>
        x ∈ (pieceFam P hw ⟨i, j⟩).carrier).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact Fin.ext (piece_unique (P i) hw (hx i) ha hb)
    exact_mod_cast this
  by_cases hxe : x ∈ enlarged (P i) w
  · by_cases hxi : x ∈ (P i).carrier
    · rw [Set.indicator_of_mem hxi, Pi.one_apply]
      exact hle1.trans le_self_add
    · have hmem : x ∈ enlarged (P i) w \ (P i).carrier := ⟨hxe, hxi⟩
      rw [Set.indicator_of_notMem hxi, Set.indicator_of_mem hmem, zero_add, Pi.one_apply]
      exact hle1
  · have h0 : ∀ j : Fin (nPieces (P i) w), (pieceFam P hw ⟨i, j⟩).carrier.indicator
        (1 : Plane → ℝ≥0∞) x = 0 := fun j =>
      Set.indicator_of_notMem (fun h => hxe (piece_subset_enlarged _ hw j.2 h)) _
    simp only [h0, Finset.sum_const_zero]
    exact zero_le

lemma measurableSet_extra (Q : Plank) (w : ℝ) :
    MeasurableSet (enlarged Q w \ Q.carrier) :=
  (measurableSet_le (by fun_prop) (by fun_prop)).diff Q.measurableSet_carrier

lemma excessF_pieceFam_le (P : ι → Plank) {w : ℝ} (hw : 0 < w) :
    excessF (pieceFam P hw) ≤ excessF P + ENNReal.ofReal (Fintype.card ι * (2 * w)) := by
  set N : Set Plane := ⋃ i, ⋃ j : ℕ,
    {x | inner ℝ x (P i).n = (P i).mid - nPieces (P i) w * w / 2 + j * w}
  have hN : volume N = 0 :=
    measure_iUnion_null fun i => measure_iUnion_null fun j => volume_line _ (P i).norm_n _
  have hae : ∀ᵐ x ∂(volume.restrict unitDisk), ((countF (pieceFam P hw) x : ℝ≥0∞) - 1) ≤
      ((countF P x : ℝ≥0∞) - 1) + ∑ i, (enlarged (P i) w \ (P i).carrier).indicator 1 x := by
    refine ae_restrict_of_ae ?_
    have : ∀ᵐ x ∂volume, x ∉ N := measure_eq_zero_iff_ae_notMem.1 hN
    filter_upwards [this] with x hx
    have hx' : ∀ i, ∀ j : ℕ, inner ℝ x (P i).n ≠
        (P i).mid - nPieces (P i) w * w / 2 + j * w := by
      intro i j h
      exact hx (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨j, h⟩⟩)
    refine (tsub_le_tsub_right (countF_pieceFam_le P hw hx') 1).trans ?_
    rw [tsub_le_iff_right]
    calc (countF P x : ℝ≥0∞) + ∑ i, (enlarged (P i) w \ (P i).carrier).indicator 1 x
        ≤ ((countF P x : ℝ≥0∞) - 1 + 1) + ∑ i, (enlarged (P i) w \ (P i).carrier).indicator 1 x := by
          gcongr; exact le_tsub_add
      _ = _ := by ring
  unfold excessF
  refine (lintegral_mono_ae hae).trans ?_
  rw [lintegral_add_right _ (Finset.measurable_sum _ fun i _ =>
    measurable_one.indicator (measurableSet_extra (P i) w))]
  gcongr
  rw [lintegral_finset_sum _ fun i _ => measurable_one.indicator (measurableSet_extra (P i) w)]
  calc ∑ i, ∫⁻ x in unitDisk, (enlarged (P i) w \ (P i).carrier).indicator 1 x
      = ∑ i, volume ((enlarged (P i) w \ (P i).carrier) ∩ unitDisk) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_indicator_one (measurableSet_extra (P i) w),
          Measure.restrict_apply (measurableSet_extra (P i) w)]
    _ ≤ ∑ _i : ι, ENNReal.ofReal (2 * w) := Finset.sum_le_sum fun i _ => volume_extra_le _ hw
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]

omit [Fintype ι] in
lemma ang_pieceFam (P : ι → Plank) {w : ℝ} (hw : 0 < w) (p q : Σ i : ι, Fin (nPieces (P i) w)) :
    (pieceFam P hw p).ang (pieceFam P hw q) = (P p.1).ang (P q.1) := rfl

/-- Nonparallel members of a finite family have angles bounded below. -/
lemma exists_angle_bound (P : ι → Plank) :
    ∃ θ > 0, ∀ i j, (P i).ang (P j) ≠ 0 → θ ≤ (P i).ang (P j) := by
  classical
  set S : Finset ℝ := (Finset.univ.image fun q : ι × ι => (P q.1).ang (P q.2)).filter (· ≠ 0)
  by_cases hS : S.Nonempty
  · refine ⟨S.min' hS, ?_, fun i j hij => S.min'_le _ ?_⟩
    · have hm := S.min'_mem hS
      simp only [S, Finset.mem_filter, Finset.mem_image] at hm
      obtain ⟨⟨q, _, hq⟩, hne⟩ := hm
      rw [← hq] at hne ⊢
      exact lt_of_le_of_ne (Plank.ang_nonneg _ _) (Ne.symm hne)
    · simp only [S, Finset.mem_filter, Finset.mem_image]
      exact ⟨⟨(i, j), Finset.mem_univ _, rfl⟩, hij⟩
  · refine ⟨1, one_pos, fun i j hij => ?_⟩
    refine absurd ⟨(P i).ang (P j), ?_⟩ hS
    simp only [S, Finset.mem_filter, Finset.mem_image]
    exact ⟨⟨(i, j), Finset.mem_univ _, rfl⟩, hij⟩

/-- Theorem 2.1 for indexed families. -/
theorem overlap_indexed (P : ι → Plank) {r : ℝ} (hr : 0 < r) (hrρ : r ≤ kRho / 2000)
    (hH : holeF P ⊆ closedBall 0 r) :
    ENNReal.ofReal (cEq / r) * volume (holeF P) ≤ excessF P := by
  obtain ⟨θ, hθ, hθP⟩ := exists_angle_bound P
  set N : ℝ := (Fintype.card ι : ℝ)
  have hc : 0 < cEq / r := div_pos cEq_pos hr
  have hA : (0 : ℝ) < kA := by norm_num [kA]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set w : ℝ := min (r / 100) (min (kRho * θ / kA) (ε / (2 * (N + 1) * (1 + cEq / r))))
  have hw : 0 < w := lt_min (by positivity) (lt_min (div_pos (mul_pos kRho_pos hθ) hA)
    (div_pos (by exact_mod_cast hε) (by positivity)))
  have hwr : w ≤ r / 100 := min_le_left _ _
  have hwθ : w ≤ kRho * θ / kA := (min_le_right _ _).trans (min_le_left _ _)
  have hwε : w ≤ ε / (2 * (N + 1) * (1 + cEq / r)) := (min_le_right _ _).trans (min_le_right _ _)
  have hsep : AngleSep (pieceFam P hw) w := by
    intro p q hpq
    rw [ang_pieceFam] at hpq ⊢
    have := hθP _ _ hpq
    rw [le_div_iff₀ hA] at hwθ
    nlinarith [kRho_pos]
  have hmain := equalWidth_overlap (pieceFam P hw) hw (pieceFam_equalWidth P hw) hr hrρ hwr hsep
    ((holeF_pieceFam_subset P hw).trans hH)
  have h1 := volume_holeF_le_pieceFam P hw
  have h2 := excessF_pieceFam_le P hw
  calc ENNReal.ofReal (cEq / r) * volume (holeF P)
      ≤ ENNReal.ofReal (cEq / r) * (volume (holeF (pieceFam P hw)) +
          ENNReal.ofReal (N * (2 * w))) := by gcongr
    _ = ENNReal.ofReal (cEq / r) * volume (holeF (pieceFam P hw)) +
          ENNReal.ofReal (cEq / r * (N * (2 * w))) := by
        rw [mul_add, ENNReal.ofReal_mul hc.le]
    _ ≤ excessF P + ENNReal.ofReal (N * (2 * w)) + ENNReal.ofReal (cEq / r * (N * (2 * w))) := by
        gcongr; exact hmain.trans h2
    _ = excessF P + ENNReal.ofReal ((1 + cEq / r) * (N * (2 * w))) := by
        rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    _ ≤ excessF P + ε := by
        gcongr
        rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal]
        rw [le_div_iff₀ (by positivity)] at hwε
        have hN : 0 ≤ N := by positivity
        nlinarith

end Family

/-- Theorem 2.1 (quantitative overlap theorem), with the constant `cEq`. -/
theorem overlap_theorem_cEq : OverlapTheoremWith cEq := by
  refine ⟨kRho / 2000, by have := kRho_pos; positivity, fun F r hr hrOv hH => ?_⟩
  rw [hole_eq_holeF] at hH ⊢
  rw [excess_eq_excessF]
  exact overlap_indexed _ hr hrOv.le hH

end Annulus

end
