module

public import RequestProject.Overlap.Carrier

/-!
# Two-line comparison for meeting carrier bands

If the carrier bands of two central planks `P_j`, `P_k` meet and `s_k ≤ s_j`, then near the
origin the thin strip around `ℓ_k` lies in a strip of half-width `1.2 ρ s_j` around `ℓ_j`.
Either the two center lines cross in `ρD` (and then their angle is at most `s_j`), or they are
parallel, or their crossing point is far away and the distance between the lines varies by a
bounded factor between the meeting point and the origin.
-/

@[expose] public section

open MeasureTheory Set Metric Real
open scoped ENNReal

noncomputable section

namespace Annulus

set_option maxHeartbeats 2000000 in
/-- The strip around `ℓ_k` near the origin is contained in the enlarged strip around `ℓ_j`. -/
theorem strip_cover {Pj Pk : Plank} {σj σk sj sk r : ℝ} (hσj : σj = 1 ∨ σj = -1)
    (hσk : σk = 1 ∨ σk = -1) (hk : |Pk.mid| ≤ 7 / 100 * kRho) (hsk0 : 0 ≤ sk)
    (hskj : sk ≤ sj) (hr : r ≤ kRho / 2000)
    (hnear : Pj.ang Pk ≠ 0 → ‖Pj.crossPt Pk‖ ≤ kRho → |inner ℝ (J Pj.n) Pk.n| ≤ sj)
    (hmeet : (carrierBand Pj σj (7 / 100 * kRho * sj) ∩
      carrierBand Pk σk (7 / 100 * kRho * sk)).Nonempty)
    {x : Plane} (hx : ‖x‖ ≤ r) (hxk : |inner ℝ x Pk.n - Pk.mid| ≤ 7 / 100 * kRho * sk) :
    |inner ℝ x Pj.n - Pj.mid| ≤ 6 / 5 * kRho * sj := by
  have hρ := kRho_pos
  obtain ⟨p, hpj, hpk⟩ := hmeet
  have hdpj := abs_sub_mid_le_of_mem_carrierBand hσj hpj
  have hdpk := abs_sub_mid_le_of_mem_carrierBand hσk hpk
  have hpJ : |inner ℝ p (J Pk.n)| ≤ 3 / 5 * kRho := hpk.1
  have hxJ : |inner ℝ x (J Pk.n)| ≤ r :=
    (abs_inner_le_norm_of_unit (by rw [norm_J, Pk.norm_n]) x).trans hx
  have hsj0 : 0 ≤ sj := hsk0.trans hskj
  have hσ : |inner ℝ (J Pk.n) Pj.n| = |inner ℝ (J Pj.n) Pk.n| := inner_J_comm_abs _ _
  have hcnn : |inner ℝ Pk.n Pj.n| ≤ 1 := abs_inner_le_one Pk.norm_n Pj.norm_n
  have hhk : 7 / 100 * kRho * sk ≤ 7 / 100 * kRho * sj := by gcongr
  by_cases hfar : Pj.ang Pk ≠ 0 ∧ kRho < ‖Pj.crossPt Pk‖
  · -- far crossing point
    obtain ⟨hang, hc⟩ := hfar
    set c := Pj.crossPt Pk with hc_def
    have hcj : inner ℝ c Pj.n = Pj.mid := Plank.crossPt_mem_left Pj Pk
    have hck : inner ℝ c Pk.n = Pk.mid := Plank.crossPt_mem_right hang
    have hdec : ∀ y : Plane, inner ℝ y Pj.n - Pj.mid =
        (inner ℝ y Pk.n - Pk.mid) * inner ℝ Pk.n Pj.n +
          (inner ℝ y (J Pk.n) - inner ℝ c (J Pk.n)) * inner ℝ (J Pk.n) Pj.n := by
      intro y
      have := inner_decomp Pk.norm_n (y - c) Pj.n
      simp only [inner_sub_left, hcj, hck] at this
      exact this
    set C := inner ℝ c (J Pk.n) with hC_def
    have hCsq : kRho ^ 2 < Pk.mid ^ 2 + C ^ 2 := by
      rw [← Plank.norm_sq_of_mem_centerLine (Plank.crossPt_mem_right hang)]
      exact pow_lt_pow_left₀ hc hρ.le two_ne_zero
    have hmk : Pk.mid ^ 2 ≤ (7 / 100 * kRho) ^ 2 := by rw [← sq_abs]; gcongr
    have hC : 99 / 100 * kRho < |C| := by
      have : (99 / 100 * kRho) ^ 2 < |C| ^ 2 := by rw [sq_abs]; nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) this
    -- `τ(p)` and `τ(x)`
    have hτp : |C| - 3 / 5 * kRho ≤ |inner ℝ p (J Pk.n) - C| := by
      have := abs_sub_abs_le_abs_sub C (inner ℝ p (J Pk.n))
      rw [abs_sub_comm] at this; linarith
    have hτx : |inner ℝ x (J Pk.n) - C| ≤ r + |C| := by
      refine (abs_sub _ _).trans ?_; linarith
    have hτ3 : |inner ℝ x (J Pk.n) - C| ≤ 3 * |inner ℝ p (J Pk.n) - C| := by linarith
    have hτpσ : |inner ℝ p (J Pk.n) - C| * |inner ℝ (J Pk.n) Pj.n| ≤
        2 * (7 / 100 * kRho * sj) := by
      have h := hdec p
      have : (inner ℝ p (J Pk.n) - C) * inner ℝ (J Pk.n) Pj.n =
          (inner ℝ p Pj.n - Pj.mid) - (inner ℝ p Pk.n - Pk.mid) * inner ℝ Pk.n Pj.n := by
        linarith
      rw [← abs_mul, this]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul]
      have : |inner ℝ p Pk.n - Pk.mid| * |inner ℝ Pk.n Pj.n| ≤ 7 / 100 * kRho * sj := by
        calc _ ≤ |inner ℝ p Pk.n - Pk.mid| * 1 := by gcongr
          _ ≤ _ := by linarith
      linarith
    have h1 := hdec x
    have h2 : |inner ℝ x Pj.n - Pj.mid| ≤ |inner ℝ x Pk.n - Pk.mid| +
        |inner ℝ x (J Pk.n) - C| * |inner ℝ (J Pk.n) Pj.n| := by
      rw [h1]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      gcongr
      calc _ ≤ |inner ℝ x Pk.n - Pk.mid| * 1 := by gcongr
        _ = _ := mul_one _
    have h3 : |inner ℝ x (J Pk.n) - C| * |inner ℝ (J Pk.n) Pj.n| ≤
        3 * (|inner ℝ p (J Pk.n) - C| * |inner ℝ (J Pk.n) Pj.n|) := by
      rw [← mul_assoc]; gcongr
    have : 0 ≤ kRho * sj := by positivity
    linarith
  · -- the center lines are parallel or cross in `ρD`
    have hsjk : |inner ℝ (J Pj.n) Pk.n| ≤ sj := by
      by_cases hang : Pj.ang Pk ≠ 0
      · exact hnear hang (by push_neg at hfar; exact hfar hang)
      · push_neg at hang
        have := (Plank.ang_ne_zero_iff Pj Pk).not.1 (by rw [hang]; simp)
        push_neg at this
        rw [this, abs_zero]; exact hsj0
    have hdec := inner_decomp Pk.norm_n (x - p) Pj.n
    simp only [inner_sub_left] at hdec
    have h1 : |inner ℝ x Pk.n - inner ℝ p Pk.n| ≤ 2 * (7 / 100 * kRho * sj) := by
      have : inner ℝ x Pk.n - inner ℝ p Pk.n =
          (inner ℝ x Pk.n - Pk.mid) - (inner ℝ p Pk.n - Pk.mid) := by ring
      rw [this]; refine (abs_sub _ _).trans ?_; linarith
    have h2 : |inner ℝ x (J Pk.n) - inner ℝ p (J Pk.n)| ≤ 601 / 1000 * kRho := by
      refine (abs_sub _ _).trans ?_; linarith
    have h3 : |inner ℝ x Pj.n - inner ℝ p Pj.n| ≤
        2 * (7 / 100 * kRho * sj) + 601 / 1000 * kRho * sj := by
      rw [hdec]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, hσ]
      have : |inner ℝ x Pk.n - inner ℝ p Pk.n| * |inner ℝ Pk.n Pj.n| ≤
          2 * (7 / 100 * kRho * sj) := by
        calc _ ≤ |inner ℝ x Pk.n - inner ℝ p Pk.n| * 1 := by gcongr
          _ ≤ _ := by linarith
      have : |inner ℝ x (J Pk.n) - inner ℝ p (J Pk.n)| * |inner ℝ (J Pj.n) Pk.n| ≤
          601 / 1000 * kRho * sj := by
        calc _ ≤ 601 / 1000 * kRho * |inner ℝ (J Pj.n) Pk.n| := by gcongr
          _ ≤ _ := by gcongr
      linarith
    have : inner ℝ x Pj.n - Pj.mid = (inner ℝ x Pj.n - inner ℝ p Pj.n) +
        (inner ℝ p Pj.n - Pj.mid) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    nlinarith

end Annulus

end
