module

public import RequestProject.Overlap.Cells

/-!
# Carrier bands (Lemma 4.8)

For a surviving candidate pair `(P_k, P_l)` whose angle is maximal among the candidate
partners of `P_k`, the one-sided band of height `h = 0.07 ρ s` beside `ℓ_k` (with
`s = sin ang(P_k, P_l)`) lies in the hull `K₀`; every survivor meeting the band belongs to
`N(P_k, P_l)`, so by non-removability the band is almost entirely hole.
-/

@[expose] public section

open MeasureTheory Set Metric Real
open scoped ENNReal

noncomputable section

namespace Annulus

/-- The one-sided carrier band `{|u| ≤ 0.6 ρ, 0 ≤ v ≤ h}` beside `ℓ_Q`, on the side `σ`. -/
def carrierBand (Q : Plank) (σ h : ℝ) : Set Plane :=
  {x | |inner ℝ x (J Q.n)| ≤ 3 / 5 * kRho ∧ 0 ≤ σ * (inner ℝ x Q.n - Q.mid) ∧
    σ * (inner ℝ x Q.n - Q.mid) ≤ h}

lemma sigma_sq {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : σ * σ = 1 := by
  rcases hσ with rfl | rfl <;> norm_num

lemma abs_sigma {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : |σ| = 1 := by
  rcases hσ with rfl | rfl <;> norm_num

lemma abs_sub_mid_le_of_mem_carrierBand {Q : Plank} {σ h : ℝ} (hσ : σ = 1 ∨ σ = -1) {x : Plane}
    (hx : x ∈ carrierBand Q σ h) : |inner ℝ x Q.n - Q.mid| ≤ h := by
  have e : |inner ℝ x Q.n - Q.mid| = |σ * (inner ℝ x Q.n - Q.mid)| := by
    rw [abs_mul, abs_sigma hσ, one_mul]
  rw [e, abs_of_nonneg hx.2.1]; exact hx.2.2

lemma norm_le_of_mem_carrierBand {Q : Plank} {σ h : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hQ : |Q.mid| ≤ 7 / 100 * kRho) (hh : h ≤ 7 / 100 * kRho) {x : Plane}
    (hx : x ∈ carrierBand Q σ h) : ‖x‖ ≤ 62 / 100 * kRho := by
  have hρ := kRho_pos
  have h1 := abs_sub_mid_le_of_mem_carrierBand hσ hx
  have h2 : |inner ℝ x Q.n| ≤ 14 / 100 * kRho := by
    have := abs_sub_abs_le_abs_sub (inner ℝ x Q.n) Q.mid; linarith
  have h3 := hx.1
  have hsq : ‖x‖ ^ 2 ≤ (62 / 100 * kRho) ^ 2 := by
    rw [norm_sq_frame Q.norm_n x]
    have : inner ℝ x Q.n ^ 2 ≤ (14 / 100 * kRho) ^ 2 := by
      rw [← sq_abs]; gcongr
    have : inner ℝ x (J Q.n) ^ 2 ≤ (3 / 5 * kRho) ^ 2 := by
      rw [← sq_abs]; gcongr
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq

lemma measurableSet_carrierBand (Q : Plank) (σ h : ℝ) : MeasurableSet (carrierBand Q σ h) := by
  have hm1 : Measurable fun x : Plane => inner ℝ x (J Q.n) :=
    (continuous_id.inner continuous_const).measurable
  have hm2 : Measurable fun x : Plane => σ * (inner ℝ x Q.n - Q.mid) :=
    (continuous_const.mul ((continuous_id.inner continuous_const).sub continuous_const)).measurable
  exact (measurableSet_le hm1.abs measurable_const).inter
    ((measurableSet_le measurable_const hm2).inter (measurableSet_le hm2 measurable_const))

/-- Lower bound for the area of a carrier band. -/
lemma le_volume_carrierBand (Q : Plank) {σ h : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ENNReal.ofReal (6 / 5 * kRho * h) ≤ volume (carrierBand Q σ h) := by
  have hρ := kRho_pos
  have hnn : inner ℝ Q.n Q.n = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, Q.norm_n]; norm_num
  have hJJ : inner ℝ (J Q.n) (J Q.n) = (1 : ℝ) := by rw [inner_J_J, hnn]
  have h' := le_volume_of_frame_rect (c := Q.mid • Q.n) (norm_neg_smul_J hσ Q.norm_n)
    (S := carrierBand Q σ h) (a := -(3 / 5 * kRho)) (b := 3 / 5 * kRho) (a' := 0) (b' := h)
    (by linarith) (fun p hp1 hp2 => by
      simp only [frame, J_smul_J]
      have e1 : inner ℝ (Q.mid • Q.n + p.1 • -σ • J Q.n + p.2 • σ • Q.n) (J Q.n) =
          -σ * p.1 := by
        simp only [inner_add_left, inner_smul_left, inner_self_J, hJJ,
          RCLike.conj_to_real]
        ring
      have e2 : inner ℝ (Q.mid • Q.n + p.1 • -σ • J Q.n + p.2 • σ • Q.n) Q.n - Q.mid =
          σ * p.2 := by
        simp only [inner_add_left, inner_smul_left, inner_J_self, hnn,
          RCLike.conj_to_real]
        ring
      refine ⟨?_, ?_, ?_⟩
      · rw [e1, abs_mul, abs_neg, abs_sigma hσ, one_mul, abs_le]
        exact ⟨hp1.1, hp1.2⟩
      · rw [e2, ← mul_assoc, sigma_sq hσ, one_mul]; exact hp2.1
      · rw [e2, ← mul_assoc, sigma_sq hσ, one_mul]; exact hp2.2)
  refine le_trans (le_of_eq ?_) h'
  congr 1; ring

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
set_option maxHeartbeats 2000000 in
/-- Lemma 4.8: the carrier band of a maximal surviving candidate pair is almost hole. -/
theorem carrier_band (P : ι → Plank) {w : ℝ} (hw0 : 0 < w) (hw : EqualWidth P w)
    (hsep : AngleSep P w) {S : Finset ι} {k l : ι} (hcand : IsCandidate P k l)
    (hnr : ¬ IsRemovable P k l)
    (hmax : ∀ m ∈ S, IsCandidate P k m →
      |inner ℝ (J (P k).n) (P m).n| ≤ |inner ℝ (J (P k).n) (P l).n|) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      volume (carrierBand (P k) σ (7 / 100 * kRho * |inner ℝ (J (P k).n) (P l).n|) \
          holeS P S) ≤
        ENNReal.ofReal (kTau * (8 * kRho ^ 2 * |inner ℝ (J (P k).n) (P l).n|)) ∧
      carrierBand (P k) σ (7 / 100 * kRho * |inner ℝ (J (P k).n) (P l).n|) ⊆ ball 0 1 := by
  classical
  obtain ⟨hkl, hcen, hdeep, hang, c, hc, hck, hcl⟩ := hcand
  have hρ := kRho_pos
  set s := |inner ℝ (J (P k).n) (P l).n| with hs_def
  set n := (P k).n with hn_def
  have hs0 : 0 < s := Plank.sin_ang_pos hang
  have hs1 : s ≤ 1 := Plank.sin_ang_le_one _ _
  set h := 7 / 100 * kRho * s with hh_def
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 7 / 100 * kRho := by
    have := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ 7 / 100 * kRho)
    simpa [hh_def] using this
  -- `w` is tiny
  have hβ := Plank.ang_nonneg (P k) (P l)
  have hβ2 := Plank.ang_le (P k) (P l)
  have hwsep := hsep k l hang
  have hsβ : (P k).ang (P l) / 2 ≤ s := by
    have h1 := two_div_pi_mul_le_sin hβ hβ2
    rw [Plank.sin_ang] at h1
    have h2 : 1 / 2 ≤ 2 / π := by rw [le_div_iff₀ pi_pos]; linarith [pi_le_four]
    nlinarith
  have hwh : w / 2 ≤ h := by
    norm_num [kA] at hwsep
    simp only [hh_def]
    nlinarith
  have hwρ : w ≤ kRho / 1000 := by
    norm_num [kA] at hwsep
    nlinarith [pi_le_four]
  have hcP : c ∈ chord (P k) := ⟨hck, mem_closedBall_zero_iff.2 hc⟩
  have hcQ : c ∈ chord (P l) := ⟨hcl, mem_closedBall_zero_iff.2 hc⟩
  obtain ⟨σ, hσ, hrect⟩ := rect_mem_hull hcen hdeep hck hcl hs0
  -- the band lies in the hull
  have hband_hull : carrierBand (P k) σ h ⊆ hull (P k) (P l) := by
    intro x hx
    have hu : |inner ℝ x (J n)| ≤ 3 / 5 * kRho := hx.1
    have hv : σ * (inner ℝ x n - (P k).mid) ≤ 11 / 100 * kRho * s := by
      have := hx.2.2
      have : h ≤ 11 / 100 * kRho * s := by simp only [hh_def]; nlinarith
      linarith
    have := hrect _ _ hu hx.2.1 hv
    convert this using 1
    rw [← mul_assoc, sigma_sq hσ, one_mul]
    conv_lhs => rw [decomp_frame (P k).norm_n x]
    module
  have hhull := hull_subset_strip hcP hcQ
  have hband_ball : carrierBand (P k) σ h ⊆ ball 0 1 := by
    intro x hx
    have := (hhull (hband_hull hx)).1
    rw [mem_closedBall_zero_iff] at this
    rw [mem_ball_zero_iff]
    have : kRho < 1 := by norm_num [kRho]
    linarith
  refine ⟨σ, hσ, ?_, hband_ball⟩
  -- every survivor meeting the band belongs to `N(P_k, P_l)`
  have hsub : carrierBand (P k) σ h \ holeS P S ⊆
      hull (P k) (P l) ∩ ⋃ m ∈ nbhdFam P k l, (P m).carrier := by
    rintro x ⟨hx, hxH⟩
    refine ⟨hband_hull hx, ?_⟩
    have hxS : ∃ m ∈ S, x ∈ (P m).carrier := by
      by_contra hcon
      push_neg at hcon
      exact hxH ⟨hband_ball hx, by simpa using hcon⟩
    obtain ⟨m, hmS, hxm⟩ := hxS
    simp only [mem_iUnion]
    refine ⟨m, ?_, hxm⟩
    by_contra hmN
    simp only [nbhdFam, mem_setOf_eq, not_lt, le_min_iff] at hmN
    have hgt : (P k).ang (P l) < (P k).ang (P m) := by
      rw [Plank.ang_comm (P k) (P m)]
      have : 0 < (P k).ang (P l) := lt_of_le_of_ne hβ (Ne.symm hang)
      linarith [hmN.1]
    have hsin : s < |inner ℝ (J n) (P m).n| := by
      rw [← Plank.sin_ang, hs_def, ← Plank.sin_ang]
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [pi_pos]) (Plank.ang_le _ _) hgt
    have hangm : (P k).ang (P m) ≠ 0 := by linarith [hβ]
    have hxnorm := norm_le_of_mem_carrierBand hσ hcen hh1 hx
    have hcand' : IsCandidate P k m := by
      refine ⟨?_, hcen, ?_, hangm, (P k).crossPt (P m), ?_, Plank.crossPt_mem_left _ _,
        Plank.crossPt_mem_right hangm⟩
      · rintro rfl
        rw [inner_J_self, abs_zero] at hsin
        linarith
      · have := Plank.abs_mid_le_of_mem_carrier hxm
        rw [hw m] at this
        unfold IsDeep
        linarith
      · have hsm : 0 < |inner ℝ (J n) (P m).n| := by linarith
        have h1 : |inner ℝ x (P k).n - (P k).mid| ≤ h := abs_sub_mid_le_of_mem_carrierBand hσ hx
        have h2 : |inner ℝ x (P m).n - (P m).mid| ≤ h := by
          have := (P m).mem_carrier_iff x |>.1 hxm
          rw [hw m] at this; linarith
        have h3 := Plank.norm_sub_crossPt_le hangm h1 h2
        have h4 : 2 * h / |inner ℝ (J n) (P m).n| ≤ 14 / 100 * kRho := by
          rw [div_le_iff₀ hsm]
          simp only [hh_def]
          nlinarith
        have h5 : ‖(P k).crossPt (P m)‖ ≤ ‖x‖ + ‖x - (P k).crossPt (P m)‖ := by
          calc ‖(P k).crossPt (P m)‖ = ‖x - (x - (P k).crossPt (P m))‖ := by rw [sub_sub_cancel]
            _ ≤ _ := norm_sub_le _ _
        linarith
    have := hmax m hmS hcand'
    linarith
  -- non-removability
  have hlt : volume (hull (P k) (P l) ∩ ⋃ m ∈ nbhdFam P k l, (P m).carrier) <
      ENNReal.ofReal kTau * volume (hull (P k) (P l)) := by
    by_contra hcon
    push_neg at hcon
    exact hnr ⟨⟨hkl, hcen, hdeep, hang, c, hc, hck, hcl⟩, hcon⟩
  calc volume (carrierBand (P k) σ h \ holeS P S)
      ≤ volume (hull (P k) (P l) ∩ ⋃ m ∈ nbhdFam P k l, (P m).carrier) := measure_mono hsub
    _ ≤ ENNReal.ofReal kTau * volume (hull (P k) (P l)) := hlt.le
    _ ≤ ENNReal.ofReal kTau * ENNReal.ofReal (8 * kRho ^ 2 * s) := by
        gcongr; exact volume_hull_le hcP hcQ
    _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num [kTau])]

end Annulus

end
