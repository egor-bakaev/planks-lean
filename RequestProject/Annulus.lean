module

public import Mathlib

/-!
# Bezdek's annulus theorem (reduction to the quantitative overlap theorem)

This file formalizes Section 7 ("From area stability to Bezdek's width theorem") of
`area_stability_formalization.tex`:

* planks, the hole `H(𝒫)`, the counting function `M_𝒫` and the excess-overlap cost `I(𝒫)`;
* the relative-width measure `dμ = dx / (2π √(1 - ‖x‖²))` on the unit disk and
  Lemma 7.1: `μ(P) = w(P)/2` for planks whose normal interval lies in `[-1, 1]`;
* Theorem 7.2 (Bezdek's annulus theorem), derived from the quantitative overlap theorem
  (Theorem 2.1), which enters as an explicit hypothesis.
-/

@[expose] public section

open MeasureTheory Set Metric Real
open scoped ENNReal

noncomputable section

namespace Annulus

/-- The Euclidean plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A planar plank `P(n,a,b) = {x : a ≤ ⟪x, n⟫ ≤ b}` with unit normal `n` and `a ≤ b`. -/
structure Plank where
  n : Plane
  norm_n : ‖n‖ = 1
  a : ℝ
  b : ℝ
  a_le_b : a ≤ b

namespace Plank

/-- The closed set of points of the plank. -/
def carrier (P : Plank) : Set Plane := {x | P.a ≤ inner ℝ x P.n ∧ inner ℝ x P.n ≤ P.b}

/-- The width `w(P) = b - a` of the plank. -/
def width (P : Plank) : ℝ := P.b - P.a

end Plank

/-- The closed unit disk `D`. -/
def unitDisk : Set Plane := closedBall 0 1

/-- The hole `H(𝒫) = D \ ⋃_{P ∈ 𝒫} P`. -/
def hole (F : Finset Plank) : Set Plane := unitDisk \ ⋃ P ∈ F, P.carrier

open Classical in
/-- The counting function `M_𝒫(x) = #{P ∈ 𝒫 : x ∈ P}`. -/
def count (F : Finset Plank) (x : Plane) : ℕ := (F.filter (fun P => x ∈ P.carrier)).card

/-- The excess-overlap cost `I(𝒫) = ∫_D (M_𝒫(x) - 1)₊ dx`
(truncated subtraction in `ℝ≥0∞` is exactly the positive part). -/
def excess (F : Finset Plank) : ℝ≥0∞ := ∫⁻ x in unitDisk, ((count F x : ℝ≥0∞) - 1)

/-- The density `1 / (2π √(1 - ‖x‖²))` of the relative-width measure. With Lean's conventions
(`√t = 0` for `t ≤ 0` and `1/0 = 0`) it vanishes automatically outside the open unit disk. -/
def relDensity (x : Plane) : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * π * √(1 - ‖x‖ ^ 2)))

/-- The relative-width measure `dμ = dx / (2π √(1 - ‖x‖²))` on the unit disk. -/
def relWidthMeasure : Measure Plane := volume.withDensity relDensity

/-- The statement of the quantitative overlap theorem (Theorem 2.1) with constant `c`:
there is `r_ov > 0` such that for every finite family of planks with `H(𝒫) ⊆ rD`,
`0 < r < r_ov`, one has `I(𝒫) ≥ (c / r) |H(𝒫)|`. -/
def OverlapTheoremWith (c : ℝ) : Prop :=
  ∃ rOv > 0, ∀ (F : Finset Plank) (r : ℝ), 0 < r → r < rOv → hole F ⊆ closedBall 0 r →
    ENNReal.ofReal (c / r) * volume (hole F) ≤ excess F

/-- The explicit constant `c_ov = δ γ ρ² / 41600` of Theorem 2.1. -/
def cOv : ℝ := (1e-4 * 1e-14 * (1 / 12) ^ 2) / 41600

/-! ### The relative-width measure -/

lemma Plank.measurableSet_carrier (P : Plank) : MeasurableSet P.carrier := by
  have h : P.carrier = {x | P.a ≤ inner ℝ x P.n} ∩ {x | inner ℝ x P.n ≤ P.b} := rfl
  rw [h]
  exact ((isClosed_le continuous_const (continuous_id.inner continuous_const)).inter
    (isClosed_le (continuous_id.inner continuous_const) continuous_const)).measurableSet

lemma relDensity_eq_zero {x : Plane} (hx : 1 ≤ ‖x‖) : relDensity x = 0 := by
  have h : 1 - ‖x‖ ^ 2 ≤ 0 := by nlinarith
  simp [relDensity, Real.sqrt_eq_zero'.2 h]

lemma measurable_relDensity : Measurable relDensity := by
  unfold relDensity
  fun_prop

lemma relWidthMeasure_ball_compl : relWidthMeasure (ball (0 : Plane) 1)ᶜ = 0 := by
  rw [relWidthMeasure, withDensity_apply _ measurableSet_ball.compl]
  rw [setLIntegral_congr_fun (g := fun _ => 0) measurableSet_ball.compl
    (fun x hx => relDensity_eq_zero (by simpa using hx))]
  simp

lemma relWidthMeasure_inter_ball (S : Set Plane) :
    relWidthMeasure (S ∩ ball 0 1) = relWidthMeasure S :=
  measure_inter_conull relWidthMeasure_ball_compl

lemma inner_integral_relDensity (t : ℝ) :
    ∫⁻ s, ENNReal.ofReal (1 / (2 * π * √(1 - (t ^ 2 + s ^ 2)))) =
      (Ioo (-1 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (1 / 2)) t := by
  by_cases ht : t ∈ Ioo (-1 : ℝ) 1
  swap
  · rw [Set.indicator_of_notMem ht]
    have h0 : ∀ s : ℝ, ENNReal.ofReal (1 / (2 * π * √(1 - (t ^ 2 + s ^ 2)))) = 0 := by
      intro s
      have h1 : 1 ≤ t ^ 2 := by
        simp only [mem_Ioo, not_and_or, not_lt] at ht
        rcases ht with h | h <;> nlinarith
      have h : 1 - (t ^ 2 + s ^ 2) ≤ 0 := by nlinarith
      simp [Real.sqrt_eq_zero'.2 h]
    simp only [h0]
    exact lintegral_zero
  rw [Set.indicator_of_mem ht]
  obtain ⟨ht1, ht2⟩ := ht
  set c := √(1 - t ^ 2) with hc_def
  have hc : 0 < c := Real.sqrt_pos.2 (by nlinarith)
  have hc2 : c ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
  let g : ℝ → ℝ := fun s => 1 / (2 * π * √(c ^ 2 - s ^ 2))
  have hfg : ∀ s, 1 / (2 * π * √(1 - (t ^ 2 + s ^ 2))) = g s := by
    intro s; simp only [g, hc2]; ring_nf
  simp_rw [hfg]
  -- `g` vanishes outside `(-c, c)`
  have hsupp : ∀ s ∉ Ioo (-c) c, ENNReal.ofReal (g s) = 0 := by
    intro s hs
    have h : c ^ 2 - s ^ 2 ≤ 0 := by
      simp only [mem_Ioo, not_and_or, not_lt] at hs
      rcases hs with h | h <;> nlinarith
    simp [g, Real.sqrt_eq_zero'.2 h]
  have hind : (fun s => ENNReal.ofReal (g s)) =
      (Ioo (-c) c).indicator (fun s => ENNReal.ofReal (g s)) := by
    funext s
    by_cases hs : s ∈ Ioo (-c) c
    · rw [Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs, hsupp s hs]
  rw [hind, lintegral_indicator measurableSet_Ioo]
  -- antiderivative
  let G : ℝ → ℝ := fun s => Real.arcsin (s / c) / (2 * π)
  have hGcont : ContinuousOn G (Icc (-c) c) := by
    apply Continuous.continuousOn
    exact (Real.continuous_arcsin.comp (continuous_id.div_const c)).div_const _
  have hGderiv : ∀ s ∈ Ioo (-c) c, HasDerivAt G (g s) s := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hs
    have h1 : s / c ≠ -1 := by
      intro h; rw [div_eq_iff hc.ne'] at h; linarith
    have h2 : s / c ≠ 1 := by
      intro h; rw [div_eq_iff hc.ne'] at h; linarith
    have hd := ((Real.hasDerivAt_arcsin h1 h2).comp s
      ((hasDerivAt_id s).div_const c)).div_const (2 * π)
    have hnn : 0 ≤ 1 - (s / c) ^ 2 := by
      rw [sub_nonneg, div_pow, div_le_one (by positivity)]; nlinarith
    have key : √(1 - (s / c) ^ 2) * c = √(c ^ 2 - s ^ 2) := by
      have hsq : √(c ^ 2) = c := Real.sqrt_sq hc.le
      calc √(1 - (s / c) ^ 2) * c = √(1 - (s / c) ^ 2) * √(c ^ 2) := by rw [hsq]
        _ = √((1 - (s / c) ^ 2) * c ^ 2) := (Real.sqrt_mul hnn _).symm
        _ = √(c ^ 2 - s ^ 2) := by congr 1; field_simp
    convert hd using 1
    · rfl
    · change 1 / (2 * π * √(c ^ 2 - s ^ 2)) = 1 / √(1 - (s / c) ^ 2) * (1 / c) / (2 * π)
      rw [← key]
      field_simp
  have hgnn : ∀ s ∈ Ioo (-c) c, 0 ≤ g s := fun s _ => by
    simp only [g]; positivity
  have hint : IntegrableOn g (Ioc (-c) c) :=
    intervalIntegral.integrableOn_deriv_of_nonneg hGcont hGderiv hgnn
  have hval : ∫ s in (-c)..c, g s = 1 / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith) hGcont hGderiv
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2 hint)]
    simp only [G, neg_div, div_self hc.ne', Real.arcsin_one, Real.arcsin_neg]
    field_simp
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.mono_set Ioo_subset_Ioc_self)
    ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall hgnn)),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith), hval]

lemma relWidthMeasure_coordSlab (a b : ℝ) :
    relWidthMeasure {y : Plane | a ≤ y 0 ∧ y 0 ≤ b} =
      ∫⁻ t in Icc a b, (Ioo (-1 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (1 / 2)) t := by
  let e : Plane ≃ᵐ ℝ × ℝ := (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans
    MeasurableEquiv.finTwoArrow
  have hmp : MeasurePreserving e volume volume :=
    (volume_preserving_finTwoArrow ℝ).comp
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))
  have he : ∀ y : Plane, e y = (y 0, y 1) := fun y => rfl
  let F : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (1 / (2 * π * √(1 - (p.1 ^ 2 + p.2 ^ 2))))
  have hF : Measurable F := by fun_prop
  have hdens : ∀ y : Plane, relDensity y = F (e y) := by
    intro y
    simp only [relDensity, F, he, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
      Real.norm_eq_abs, sq_abs]
  have hpre : {y : Plane | a ≤ y 0 ∧ y 0 ≤ b} = e ⁻¹' (Icc a b ×ˢ univ) := by
    ext y
    simp [he]
  rw [relWidthMeasure, withDensity_apply' _, hpre]
  simp_rw [hdens]
  rw [hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding F, Measure.volume_eq_prod,
    ← Measure.prod_restrict, Measure.restrict_univ, lintegral_prod _ hF.aemeasurable]
  refine lintegral_congr (fun t => ?_)
  exact inner_integral_relDensity t

lemma relWidthMeasure_carrier_eq_coordSlab (P : Plank) :
    relWidthMeasure P.carrier = relWidthMeasure {y : Plane | P.a ≤ y 0 ∧ y 0 ≤ P.b} := by
  have hon : Orthonormal ℝ (({0} : Set (Fin 2)).domRestrict (fun _ => P.n)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst hij
    simp only [Set.domRestrict_apply, ite_true]
    rw [real_inner_self_eq_norm_mul_norm, P.norm_n, mul_one]
  obtain ⟨B, hB⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp) hon
  set T := B.repr
  have hT : ∀ x, inner ℝ x P.n = T x 0 := by
    intro x
    rw [OrthonormalBasis.repr_apply_apply, hB 0 rfl, real_inner_comm]
  have hpre : P.carrier = T ⁻¹' {y : Plane | P.a ≤ y 0 ∧ y 0 ≤ P.b} := by
    ext x
    simp [Plank.carrier, hT]
  have hmp : MeasurePreserving T volume volume := T.measurePreserving
  rw [hpre, relWidthMeasure, withDensity_apply' _, withDensity_apply' _,
    ← hmp.setLIntegral_comp_preimage_emb T.toHomeomorph.measurableEmbedding relDensity
      {y : Plane | P.a ≤ y 0 ∧ y 0 ≤ P.b}]
  congr 1
  funext x
  simp [relDensity, LinearIsometryEquiv.norm_map]

lemma relWidthMeasure_coordSlab' (a b : ℝ) :
    relWidthMeasure {y : Plane | a ≤ y 0 ∧ y 0 ≤ b} =
      ENNReal.ofReal (1 / 2) * volume (Ioo (-1 : ℝ) 1 ∩ Icc a b) := by
  rw [relWidthMeasure_coordSlab, lintegral_indicator_const measurableSet_Ioo,
    Measure.restrict_apply measurableSet_Ioo]

/-- Lemma 7.1 (relative-width measure): if the normal interval of a plank lies in `[-1, 1]`,
then `μ(P) = w(P) / 2`. -/
theorem relWidthMeasure_plank (P : Plank) (ha : -1 ≤ P.a) (hb : P.b ≤ 1) :
    relWidthMeasure P.carrier = ENNReal.ofReal (P.width / 2) := by
  rw [relWidthMeasure_carrier_eq_coordSlab, relWidthMeasure_coordSlab']
  have hvol : volume (Ioo (-1 : ℝ) 1 ∩ Icc P.a P.b) = ENNReal.ofReal (P.b - P.a) := by
    apply le_antisymm
    · exact (measure_mono inter_subset_right).trans (by rw [Real.volume_Icc])
    · rw [← Real.volume_Ioo]
      refine measure_mono (fun t ht => ⟨⟨?_, ?_⟩, ht.1.le, ht.2.le⟩) <;>
        linarith [ht.1, ht.2]
  rw [hvol, ← ENNReal.ofReal_mul (by norm_num), Plank.width]
  congr 1; ring

/-- For an arbitrary plank, `μ(P) ≤ w(P) / 2` (reduction of the plank to `[-1,1]`). -/
theorem relWidthMeasure_plank_le (P : Plank) :
    relWidthMeasure P.carrier ≤ ENNReal.ofReal (P.width / 2) := by
  rw [relWidthMeasure_carrier_eq_coordSlab, relWidthMeasure_coordSlab']
  calc ENNReal.ofReal (1 / 2) * volume (Ioo (-1 : ℝ) 1 ∩ Icc P.a P.b)
      ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal (P.b - P.a) := by
        gcongr
        exact (measure_mono inter_subset_right).trans (by rw [Real.volume_Icc])
    _ = ENNReal.ofReal (P.width / 2) := by
        rw [← ENNReal.ofReal_mul (by norm_num), Plank.width]
        congr 1; ring

/-- `μ` is a probability measure on the unit disk: `μ(D) = 1`. -/
theorem relWidthMeasure_unitDisk : relWidthMeasure unitDisk = 1 := by
  have hball : ∀ S : Set Plane, ball 0 1 ⊆ S → S ∩ ball 0 1 = ball 0 1 :=
    fun S h => inter_eq_right.2 h
  rw [← relWidthMeasure_inter_ball, hball unitDisk ball_subset_closedBall,
    ← hball {y : Plane | -1 ≤ y 0 ∧ y 0 ≤ 1} ?_, relWidthMeasure_inter_ball,
    relWidthMeasure_coordSlab', inter_eq_left.2 Ioo_subset_Icc_self, Real.volume_Ioo,
    ← ENNReal.ofReal_mul (by norm_num)]
  · norm_num
  · intro y hy
    rw [mem_ball, dist_zero_right] at hy
    have h := PiLp.norm_apply_le y 0
    rw [Real.norm_eq_abs] at h
    constructor <;> linarith [abs_le.1 (h.trans hy.le)]

/-! ### Bezdek's annulus theorem -/

/-- Theorem 7.2 (Bezdek's annulus theorem), derived from the quantitative overlap theorem with
any positive constant `c`: there is `r_* > 0` such that every finite family of planks covering
the annulus `D \ r_* D` has total width at least `2`. -/
theorem bezdek_annulus_of_overlap {c : ℝ} (hc : 0 < c) (hov : OverlapTheoremWith c) :
    ∃ rStar > 0, ∀ F : Finset Plank,
      unitDisk \ closedBall 0 rStar ⊆ ⋃ P ∈ F, P.carrier → 2 ≤ ∑ P ∈ F, P.width := by
  obtain ⟨rOv, hrOv, hov⟩ := hov
  set rStar := min (rOv / 2) (min (c / 2) (1 / 2)) with hrStar
  have hr0 : 0 < rStar := lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have hr_lt : rStar < rOv := (min_le_left _ _).trans_lt (by linarith)
  have hr_c : rStar ≤ c / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr_half : rStar ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨rStar, hr0, fun F hcover => ?_⟩
  set U := ⋃ P ∈ F, P.carrier with hU
  have hH : hole F ⊆ closedBall 0 rStar := by
    intro x hx
    by_contra h
    exact hx.2 (hcover ⟨hx.1, h⟩)
  have hmeasP : ∀ P : Plank, MeasurableSet P.carrier := Plank.measurableSet_carrier
  have hmeasU : MeasurableSet U := Finset.measurableSet_biUnion _ (fun P _ => hmeasP P)
  have hcount_eq : ∀ x, (count F x : ℝ≥0∞) = ∑ P ∈ F, P.carrier.indicator 1 x := by
    intro x
    classical
    simp only [count, Finset.card_filter, Nat.cast_sum, Set.indicator_apply]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    split_ifs <;> simp
  have hmeas_count : Measurable (fun x => (count F x : ℝ≥0∞)) := by
    simp_rw [hcount_eq]
    exact Finset.measurable_sum _ (fun P _ => measurable_one.indicator (hmeasP P))
  have hmeas_g : Measurable (fun x => (count F x : ℝ≥0∞) - 1) :=
    hmeas_count.sub measurable_const
  -- the overlap theorem
  have hexc : ENNReal.ofReal (c / rStar) * volume (hole F) ≤ excess F :=
    hov F rStar hr0 hr_lt hH
  have h2 : (2 : ℝ) ≤ c / rStar := by rw [le_div_iff₀ hr0]; linarith
  -- `μ(H) ≤ |H| / π`
  have hmuH : relWidthMeasure (hole F) ≤ ENNReal.ofReal (1 / π) * volume (hole F) := by
    rw [relWidthMeasure, withDensity_apply' _ (hole F)]
    calc ∫⁻ x in hole F, relDensity x ≤ ∫⁻ _ in hole F, ENNReal.ofReal (1 / π) := by
          refine setLIntegral_mono measurable_const (fun x hx => ?_)
          have hx' : ‖x‖ ≤ 1 / 2 := by
            have := hH hx
            rw [mem_closedBall, dist_zero_right] at this
            linarith
          have hs : 1 / 2 ≤ √(1 - ‖x‖ ^ 2) := by
            rw [Real.le_sqrt (by norm_num)] <;> nlinarith [norm_nonneg x]
          unfold relDensity
          apply ENNReal.ofReal_le_ofReal
          rw [div_le_div_iff₀ (by positivity) pi_pos]
          nlinarith [pi_pos]
      _ = ENNReal.ofReal (1 / π) * volume (hole F) := setLIntegral_const _ _
  -- `∫ (M - 1) dμ ≥ I(𝒫) / (2π)`
  have hexcμ : ENNReal.ofReal (1 / (2 * π)) * excess F ≤
      ∫⁻ x, ((count F x : ℝ≥0∞) - 1) ∂relWidthMeasure := by
    rw [relWidthMeasure, lintegral_withDensity_eq_lintegral_mul₀
      measurable_relDensity.aemeasurable hmeas_g.aemeasurable, excess,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans ?_ (setLIntegral_le_lintegral unitDisk _)
    refine lintegral_mono_ae ?_
    have hsph := Measure.addHaar_sphere (volume : Measure Plane) 0 1
    filter_upwards [(ae_restrict_iff' measurableSet_closedBall).2
      (Filter.Eventually.of_forall fun x (hx : x ∈ unitDisk) => hx),
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hsph)] with x hxD hxS
    have hx1 : ‖x‖ < 1 := by
      rw [unitDisk, mem_closedBall, dist_zero_right] at hxD
      rw [mem_sphere, dist_zero_right] at hxS
      exact lt_of_le_of_ne hxD hxS
    simp only [Pi.mul_apply]
    gcongr
    unfold relDensity
    apply ENNReal.ofReal_le_ofReal
    have hpos : 0 < √(1 - ‖x‖ ^ 2) := Real.sqrt_pos.2 (by nlinarith [norm_nonneg x])
    have hle : √(1 - ‖x‖ ^ 2) ≤ 1 := Real.sqrt_le_one.2 (by nlinarith [norm_nonneg x])
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pi_pos]
  have hgH : relWidthMeasure (hole F) ≤
      ∫⁻ x, ((count F x : ℝ≥0∞) - 1) ∂relWidthMeasure := by
    refine hmuH.trans (le_trans ?_ hexcμ)
    calc ENNReal.ofReal (1 / π) * volume (hole F)
        ≤ (ENNReal.ofReal (1 / (2 * π)) * ENNReal.ofReal (c / rStar)) * volume (hole F) := by
          gcongr
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ pi_pos (by positivity)]
          nlinarith [pi_pos]
      _ ≤ ENNReal.ofReal (1 / (2 * π)) * excess F := by
          rw [mul_assoc]; gcongr
  -- pointwise `M ≥ 𝟙_U + (M - 1)`
  have hpt : ∀ x, U.indicator 1 x + ((count F x : ℝ≥0∞) - 1) ≤ (count F x : ℝ≥0∞) := by
    intro x
    by_cases hx : x ∈ U
    · have h1 : (1 : ℝ≥0∞) ≤ count F x := by
        rw [hU, mem_iUnion₂] at hx
        obtain ⟨P, hP, hxP⟩ := hx
        classical
        have : 0 < count F x := Finset.card_pos.2 ⟨P, Finset.mem_filter.2 ⟨hP, hxP⟩⟩
        exact_mod_cast this
      rw [Set.indicator_of_mem hx, Pi.one_apply, add_tsub_cancel_of_le h1]
    · rw [Set.indicator_of_notMem hx, zero_add]
      exact tsub_le_self
  -- `D ⊆ U ∪ H`
  have hDsub : unitDisk ⊆ U ∪ hole F := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · exact Or.inr ⟨hx, hxU⟩
  have hmain : (1 : ℝ≥0∞) ≤ ∑ P ∈ F, ENNReal.ofReal (P.width / 2) := by
    calc (1 : ℝ≥0∞) = relWidthMeasure unitDisk := relWidthMeasure_unitDisk.symm
      _ ≤ relWidthMeasure (U ∪ hole F) := measure_mono hDsub
      _ ≤ relWidthMeasure U + relWidthMeasure (hole F) := measure_union_le _ _
      _ ≤ relWidthMeasure U + ∫⁻ x, ((count F x : ℝ≥0∞) - 1) ∂relWidthMeasure := by
          gcongr
      _ = ∫⁻ x, (U.indicator 1 x + ((count F x : ℝ≥0∞) - 1)) ∂relWidthMeasure := by
          rw [lintegral_add_left (measurable_one.indicator hmeasU), lintegral_indicator_one hmeasU]
      _ ≤ ∫⁻ x, (count F x : ℝ≥0∞) ∂relWidthMeasure := lintegral_mono hpt
      _ = ∑ P ∈ F, relWidthMeasure P.carrier := by
          simp_rw [hcount_eq]
          rw [lintegral_finset_sum _ (fun P _ => measurable_one.indicator (hmeasP P))]
          exact Finset.sum_congr rfl (fun P _ => lintegral_indicator_one (hmeasP P))
      _ ≤ ∑ P ∈ F, ENNReal.ofReal (P.width / 2) :=
          Finset.sum_le_sum (fun P _ => relWidthMeasure_plank_le P)
  have hw : ∀ P : Plank, 0 ≤ P.width / 2 := fun P => by
    have := P.a_le_b; unfold Plank.width; linarith
  rw [← ENNReal.ofReal_sum_of_nonneg (fun P _ => hw P), ENNReal.one_le_ofReal,
    ← Finset.sum_div] at hmain
  linarith

/-- Theorem 7.2 (Bezdek's annulus theorem), assuming the quantitative overlap theorem
(Theorem 2.1) with its explicit constant `c_ov`. -/
theorem bezdek_annulus (hov : OverlapTheoremWith cOv) :
    ∃ rStar > 0, ∀ F : Finset Plank,
      unitDisk \ closedBall 0 rStar ⊆ ⋃ P ∈ F, P.carrier → 2 ≤ ∑ P ∈ F, P.width :=
  bezdek_annulus_of_overlap (by norm_num [cOv]) hov

end Annulus

end
