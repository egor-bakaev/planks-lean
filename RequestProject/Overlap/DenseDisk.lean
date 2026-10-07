module

public import RequestProject.Overlap.Hull

/-!
# Two criteria for dense disks

* two different planks overlapping on a small disk near a point `z` of a center line make
  `B(z, w/2)` dense;
* many planks passing close to `z` make `B(z, 2s)` dense by counting mass.
-/

@[expose] public section

open MeasureTheory Set Metric Real
open scoped ENNReal

noncomputable section

namespace Annulus

variable {ι : Type*} [Fintype ι]

lemma two_le_countF (P : ι → Plank) {i j : ι} (hij : i ≠ j) {x : Plane}
    (hi : x ∈ (P i).carrier) (hj : x ∈ (P j).carrier) : 2 ≤ countF P x := by
  classical
  unfold countF
  have : ({i, j} : Finset ι) ⊆ Finset.univ.filter fun k => x ∈ (P k).carrier := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp [hi, hj]
  convert Finset.card_le_card this
  rw [Finset.card_pair hij]

lemma lintegral_countF_restrict (P : ι → Plank) (B : Set Plane) :
    ∫⁻ x in B, (countF P x : ℝ≥0∞) = ∑ i, volume ((P i).carrier ∩ B) := by
  simp_rw [countF_eq_sum]
  rw [lintegral_finset_sum _ fun i _ => measurable_one.indicator (P i).measurableSet_carrier]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_indicator_one (P i).measurableSet_carrier,
    Measure.restrict_apply (P i).measurableSet_carrier]

lemma measurable_countF_sub_one (P : ι → Plank) :
    Measurable fun x => (countF P x : ℝ≥0∞) - 1 :=
  (measurable_countF P).sub measurable_const

lemma volume_ball_mul (z : Plane) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    volume (ball z (r * s)) = ENNReal.ofReal (r ^ 2) * volume (ball z s) := by
  rw [Measure.addHaar_ball_mul_of_pos volume z hr, Measure.addHaar_ball_center volume z s,
    finrank_euclideanSpace_fin]

/-- A ball in the plane has area at most that of the circumscribed square. -/
lemma volume_ball_le_sq (z : Plane) (r : ℝ) :
    volume (ball z r) ≤ ENNReal.ofReal (4 * r ^ 2) := by
  set e : Plane := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := by simp [e]
  have hsub : ball z r ⊆ {x : Plane | |inner ℝ x e - inner ℝ z e| ≤ r} ∩ closedBall z r := by
    intro x hx
    refine ⟨?_, ball_subset_closedBall hx⟩
    simp only [mem_setOf_eq]
    rw [← inner_sub_left]
    have := abs_real_inner_le_norm (x - z) e
    rw [he, mul_one, ← dist_eq_norm] at this
    exact this.trans (mem_ball.1 hx).le
  refine (measure_mono hsub).trans ((volume_strip_inter_ball_le he _ r z r).trans ?_)
  apply ENNReal.ofReal_le_ofReal; nlinarith

/-- Criterion 1: two different planks overlapping near a point of a center line. -/
lemma isDenseDisk_pair (P : ι → Plank) {w : ℝ} (hw0 : 0 < w) (hw : EqualWidth P w)
    {iS iR : ι} (hne : iS ≠ iR) {z : Plane} (hz : z ∈ (P iS).centerLine) {ν : Plane}
    (hν : ‖ν‖ = 1) {o : ℝ}
    (hband : ∀ x : Plane, o ≤ inner ℝ x ν → inner ℝ x ν ≤ o + w / 2 → x ∈ (P iR).carrier)
    (hzo : |inner ℝ z ν - o| ≤ w / 8) (hD : ball z (w / 2) ⊆ unitDisk) :
    IsDenseDisk P kDelta z (w / 2) := by
  refine ⟨by positivity, hD, ?_⟩
  set t := o + w / 4 - inner ℝ z ν
  set m := z + t • ν
  have ht : |t| ≤ 3 * w / 8 := by
    simp only [t]
    rw [abs_le] at hzo ⊢; constructor <;> linarith [hzo.1, hzo.2]
  have hmz : ‖m - z‖ ≤ 3 * w / 8 := by
    simp only [m, add_sub_cancel_left, norm_smul, hν, mul_one, Real.norm_eq_abs]; exact ht
  have hsub : ball m (w / 8) ⊆ ball z (w / 2) := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx ⊢
    calc ‖x - z‖ = ‖(x - m) + (m - z)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖x - m‖ + ‖m - z‖ := norm_add_le _ _
      _ < w / 8 + 3 * w / 8 := by linarith
      _ = w / 2 := by ring
  have hνν : inner ℝ ν ν = 1 := by rw [real_inner_self_eq_norm_sq, hν]; norm_num
  have hcount : ∀ x ∈ ball m (w / 8), 2 ≤ countF P x := by
    intro x hx
    have hxz : ‖x - z‖ < w / 2 := by rw [← dist_eq_norm]; exact hsub hx
    apply two_le_countF P hne
    · rw [(P iS).mem_carrier_iff, hw iS, ← Plank.mem_centerLine.1 hz, ← inner_sub_left]
      have := abs_real_inner_le_norm (x - z) (P iS).n
      rw [(P iS).norm_n, mul_one] at this
      linarith
    · have hxm : |inner ℝ (x - m) ν| < w / 8 := by
        have := abs_real_inner_le_norm (x - m) ν
        rw [hν, mul_one, ← dist_eq_norm] at this
        exact lt_of_le_of_lt this (mem_ball.1 hx)
      have hmν : inner ℝ m ν = o + w / 4 := by
        simp only [m, t, inner_add_left, inner_smul_left, hνν, RCLike.conj_to_real]; ring
      have hx' : inner ℝ x ν = inner ℝ (x - m) ν + (o + w / 4) := by
        rw [inner_sub_left, hmν]; ring
      rw [abs_lt] at hxm
      exact hband x (by linarith [hxm.1]) (by linarith [hxm.2])
  have h1 : volume (ball m (w / 8)) ≤ ∫⁻ x in ball z (w / 2), ((countF P x : ℝ≥0∞) - 1) := by
    calc volume (ball m (w / 8)) = ∫⁻ _ in ball m (w / 8), (1 : ℝ≥0∞) := by
          rw [setLIntegral_const, one_mul]
      _ ≤ ∫⁻ x in ball m (w / 8), ((countF P x : ℝ≥0∞) - 1) := by
          refine setLIntegral_mono (measurable_countF_sub_one P) fun x hx => ?_
          refine ENNReal.le_sub_of_add_le_left ENNReal.one_ne_top ?_
          have := hcount x hx
          have : ((2 : ℕ) : ℝ≥0∞) ≤ (countF P x : ℝ≥0∞) := by exact_mod_cast this
          simpa [one_add_one_eq_two] using this
      _ ≤ _ := lintegral_mono_set hsub
  have h2 : volume (ball m (w / 8)) = ENNReal.ofReal ((1 / 4) ^ 2) * volume (ball z (w / 2)) := by
    rw [show w / 8 = (1 / 4) * (w / 2) by ring, volume_ball_mul m (by norm_num),
      Measure.addHaar_ball_center volume m, Measure.addHaar_ball_center volume z]
  have hB0 : volume (ball z (w / 2)) ≠ 0 := (measure_ball_pos _ _ (by positivity)).ne'
  have hBt : volume (ball z (w / 2)) ≠ ∞ := measure_ball_lt_top.ne
  calc ENNReal.ofReal kDelta * volume (ball z (w / 2))
      < ENNReal.ofReal ((1 / 4) ^ 2) * volume (ball z (w / 2)) := by
        rw [ENNReal.mul_lt_mul_iff_left hB0 hBt]
        rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
        norm_num [kDelta]
    _ = volume (ball m (w / 8)) := h2.symm
    _ ≤ _ := h1

/-- A band of width `w/2` whose edge passes within `s ≥ 2w` of `z` meets `B(z, 2s)` in area at
least `3ws/2`. -/
lemma volume_band_inter_ball {w s : ℝ} (hw0 : 0 < w) (hs : 2 * w ≤ s) {z ν : Plane}
    (hν : ‖ν‖ = 1) {o : ℝ} {S : Set Plane}
    (hband : ∀ x : Plane, o ≤ inner ℝ x ν → inner ℝ x ν ≤ o + w / 2 → x ∈ S)
    (hzo : |inner ℝ z ν - o| ≤ s) :
    ENNReal.ofReal (3 / 2 * w * s) ≤ volume (S ∩ ball z (2 * s)) := by
  set e : Plane := -J ν
  have he : ‖e‖ = 1 := by simp only [e, norm_neg, norm_J, hν]
  have hJe : J e = ν := by simp only [e, J_neg, J_J, neg_neg]
  have h := le_volume_of_frame_rect (c := z) he (S := S ∩ ball z (2 * s))
    (a := -(3 / 2 * s)) (b := 3 / 2 * s) (a' := o - inner ℝ z ν)
    (b' := o - inner ℝ z ν + w / 2) (by linarith) (fun p hp1 hp2 => by
      have hin := frame_inner_Je (c := z) he p
      rw [hJe, inner_sub_left] at hin
      refine ⟨hband _ (by linarith [hp2.1]) (by linarith [hp2.2]), ?_⟩
      rw [mem_ball, dist_eq_norm]
      have hn := norm_frame_sub_sq (c := z) he p
      have h1 : p.1 ^ 2 ≤ (3 / 2 * s) ^ 2 := by
        rw [← sq_abs]; gcongr; rw [abs_le]; exact ⟨hp1.1, hp1.2⟩
      have h2 : p.2 ^ 2 ≤ (5 / 4 * s) ^ 2 := by
        rw [← sq_abs]; gcongr
        rw [abs_le] at hzo ⊢
        constructor <;> linarith [hp2.1, hp2.2, hzo.1, hzo.2]
      have hs0 : 0 < s := by linarith
      have : ‖frame z e p - z‖ ^ 2 < (2 * s) ^ 2 := by nlinarith
      exact (sq_lt_sq₀ (norm_nonneg _) (by linarith)).mp this)
  refine le_trans (le_of_eq ?_) h
  congr 1; ring

/-- Criterion 2: at least `12 s / w` planks pass within `s` of `z`. -/
lemma isDenseDisk_cluster (P : ι → Plank) {w : ℝ} (hw0 : 0 < w)
    {z : Plane} {s : ℝ} (hs : 2 * w ≤ s) (T : Finset ι) (ν : ι → Plane)
    (hν : ∀ i ∈ T, ‖ν i‖ = 1) (o : ι → ℝ)
    (hband : ∀ i ∈ T, ∀ x : Plane, o i ≤ inner ℝ x (ν i) → inner ℝ x (ν i) ≤ o i + w / 2 →
      x ∈ (P i).carrier)
    (hzo : ∀ i ∈ T, |inner ℝ z (ν i) - o i| ≤ s) (hT : 12 * s / w ≤ T.card)
    (hD : ball z (2 * s) ⊆ unitDisk) : IsDenseDisk P kDelta z (2 * s) := by
  have hs0 : 0 < s := by linarith
  refine ⟨by positivity, hD, ?_⟩
  set B := ball z (2 * s)
  have hmass : ENNReal.ofReal (18 * s ^ 2) ≤ ∫⁻ x in B, (countF P x : ℝ≥0∞) := by
    rw [lintegral_countF_restrict]
    calc ENNReal.ofReal (18 * s ^ 2) ≤ ∑ _i ∈ T, ENNReal.ofReal (3 / 2 * w * s) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [div_le_iff₀ hw0] at hT
          nlinarith
      _ ≤ ∑ i ∈ T, volume ((P i).carrier ∩ B) :=
          Finset.sum_le_sum fun i hi => volume_band_inter_ball hw0 hs (hν i hi) (hband i hi)
            (hzo i hi)
      _ ≤ ∑ i, volume ((P i).carrier ∩ B) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => zero_le
  have hB : volume B ≤ ENNReal.ofReal (16 * s ^ 2) :=
    (volume_ball_le_sq z (2 * s)).trans (ENNReal.ofReal_le_ofReal (by nlinarith))
  have hBt : volume B ≠ ∞ := measure_ball_lt_top.ne
  have hsub : ∫⁻ x in B, (countF P x : ℝ≥0∞) ≤
      (∫⁻ x in B, ((countF P x : ℝ≥0∞) - 1)) + volume B := by
    calc ∫⁻ x in B, (countF P x : ℝ≥0∞) ≤ ∫⁻ x in B, (((countF P x : ℝ≥0∞) - 1) + 1) :=
          lintegral_mono fun x => le_tsub_add
      _ = _ := by rw [lintegral_add_right _ measurable_const, setLIntegral_const, one_mul]
  have hδ : ENNReal.ofReal kDelta * volume B + volume B < ENNReal.ofReal (18 * s ^ 2) := by
    calc ENNReal.ofReal kDelta * volume B + volume B
        ≤ ENNReal.ofReal kDelta * ENNReal.ofReal (16 * s ^ 2) + ENNReal.ofReal (16 * s ^ 2) := by
          gcongr
      _ = ENNReal.ofReal ((1 + kDelta) * (16 * s ^ 2)) := by
          rw [← ENNReal.ofReal_mul (by norm_num [kDelta]),
            ← ENNReal.ofReal_add (by norm_num [kDelta]; positivity) (by positivity)]
          ring_nf
      _ < ENNReal.ofReal (18 * s ^ 2) := by
          rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
          norm_num [kDelta]; nlinarith
  have := lt_of_lt_of_le hδ (hmass.trans hsub)
  exact (ENNReal.add_lt_add_iff_right hBt).1 this

end Annulus

end
