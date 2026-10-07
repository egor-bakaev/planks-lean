module

public import RequestProject.Overlap.Arm

/-!
# Removable pairs pay overlap (Proposition 5.1)

Planks of `N(P,Q) \ {P,Q}` cover a definite part of the hull `K₀`; each of them contains a
half-width band along a line which meets one of the two chords.  Along the arm met by at least
half of these lines, the dense region occupies a definite area (`arm_pays`).
-/

@[expose] public section

open MeasureTheory Set Metric Real
open scoped ENNReal

noncomputable section

namespace Annulus

variable {ι : Type*} [Fintype ι]

/-- A plank containing `y` contains a half-width band along the line through `y` parallel to
its center line, on the side of the center line. -/
lemma exists_band_of_mem_carrier {Q : Plank} {w : ℝ} (hw : Q.width = w) {y p : Plane}
    (hy : y ∈ Q.carrier) (hp : inner ℝ p Q.n = inner ℝ y Q.n) :
    ∃ ν : Plane, ∃ o : ℝ, (ν = Q.n ∨ ν = -Q.n) ∧ inner ℝ p ν = o ∧
      ∀ x : Plane, o ≤ inner ℝ x ν → inner ℝ x ν ≤ o + w / 2 → x ∈ Q.carrier := by
  rw [Q.mem_carrier_iff, hw, abs_le] at hy
  rcases le_or_gt (inner ℝ y Q.n) Q.mid with h | h
  · refine ⟨Q.n, inner ℝ y Q.n, Or.inl rfl, hp, fun x h1 h2 => ?_⟩
    rw [Q.mem_carrier_iff, hw, abs_le]
    constructor <;> linarith [hy.1, hy.2]
  · refine ⟨-Q.n, -inner ℝ y Q.n, Or.inr rfl, by rw [inner_neg_right, hp], fun x h1 h2 => ?_⟩
    rw [inner_neg_right] at h1 h2
    rw [Q.mem_carrier_iff, hw, abs_le]
    constructor <;> linarith [hy.1, hy.2]

omit [Fintype ι] in
/-- Members of `N(P,Q)` make a small angle with both `P` and `Q`. -/
lemma sin_bound_of_mem_nbhdFam (P : ι → Plank) {i j k : ι} (hk : k ∈ nbhdFam P i j) :
    |inner ℝ (J (P i).n) (P k).n| ≤ 3 * |inner ℝ (J (P i).n) (P j).n| ∧
    |inner ℝ (J (P j).n) (P k).n| ≤ 3 * |inner ℝ (J (P i).n) (P j).n| := by
  have hsβ := (P i).sin_ang (P j)
  have hs0 : 0 ≤ |inner ℝ (J (P i).n) (P j).n| := abs_nonneg _
  have hji : |inner ℝ (J (P j).n) (P i).n| = |inner ℝ (J (P i).n) (P j).n| :=
    inner_J_comm_abs _ _
  simp only [nbhdFam, mem_setOf_eq] at hk
  rcases min_lt_iff.1 hk with h | h
  · have h1 := sin_le_two_sin (Plank.ang_nonneg _ _) (Plank.ang_le _ _)
      (Plank.ang_le (P i) (P j)) h.le
    rw [Plank.sin_ang, hsβ, inner_J_comm_abs] at h1
    have h2 := abs_inner_J_triangle (P j).norm_n (P i).norm_n (P k).n (P k).norm_n
    constructor <;> linarith
  · have h1 := sin_le_two_sin (Plank.ang_nonneg _ _) (Plank.ang_le _ _)
      (Plank.ang_le (P i) (P j)) h.le
    rw [Plank.sin_ang, hsβ, inner_J_comm_abs] at h1
    have h2 := abs_inner_J_triangle (P i).norm_n (P j).norm_n (P k).n (P k).norm_n
    constructor <;> linarith

set_option maxHeartbeats 2000000 in
/-- Proposition 5.1: a removable pair pays a fixed amount of dense area. -/
theorem removable_pays (P : ι → Plank) {w : ℝ} (hw0 : 0 < w) (hwρ : w ≤ kRho / 100)
    (hw : EqualWidth P w) {i j : ι} (hrem : IsRemovable P i j)
    (hsep : kA * w ≤ kRho * (P i).ang (P j)) :
    ENNReal.ofReal (kGamma * kRho * w) ≤
      volume (denseRegion P kDelta ∩ ((P i).carrier ∪ (P j).carrier) ∩
        closedBall 0 (5 * kRho)) := by
  classical
  obtain ⟨⟨hij, hcen, hdeep, hang, c, hc, hci, hcj⟩, hcov⟩ := hrem
  have hρ := kRho_pos
  set s := |inner ℝ (J (P i).n) (P j).n| with hs_def
  have hs0 : 0 < s := Plank.sin_ang_pos hang
  have hs1 : s ≤ 1 := Plank.sin_ang_le_one _ _
  -- lower bound on `s`
  have hsA : kA * w ≤ 2 * kRho * s := by
    have h1 := two_div_pi_mul_le_sin (Plank.ang_nonneg (P i) (P j)) (Plank.ang_le _ _)
    rw [Plank.sin_ang] at h1
    have hpi : π ≤ 4 := pi_le_four
    have h2 : 1 / 2 ≤ 2 / π := by rw [le_div_iff₀ pi_pos]; linarith
    have hb : 1 / 2 * (P i).ang (P j) ≤ s :=
      le_trans (mul_le_mul_of_nonneg_right h2 (Plank.ang_nonneg _ _)) h1
    nlinarith [mul_le_mul_of_nonneg_left hb hρ.le]
  have hcP : c ∈ chord (P i) := ⟨hci, mem_closedBall_zero_iff.2 hc⟩
  have hcQ : c ∈ chord (P j) := ⟨hcj, mem_closedBall_zero_iff.2 hc⟩
  set K := hull (P i) (P j) with hK_def
  have hKge := volume_hull_ge hcen hdeep hci hcj hs0
  have hKsub := hull_subset_strip hcP hcQ
  have hstrip : ∀ k, volume (K ∩ (P k).carrier) ≤ ENNReal.ofReal (2 * kRho * w) := by
    intro k
    calc volume (K ∩ (P k).carrier)
        ≤ volume ({x | |inner ℝ x (P k).n - (P k).mid| ≤ w / 2} ∩ closedBall 0 kRho) := by
          apply measure_mono
          rintro x ⟨hxK, hxk⟩
          refine ⟨?_, (hKsub hxK).1⟩
          rw [Plank.mem_carrier_iff, hw k] at hxk; exact hxk
      _ ≤ ENNReal.ofReal (4 * kRho * (w / 2)) := volume_strip_inter_ball_le (P k).norm_n _ _ _ _
      _ = _ := by congr 1; ring
  set Nf := Finset.univ.filter (fun k => k ∈ nbhdFam P i j) with hNf
  set T0 := Nf.filter (fun k => k ≠ i ∧ k ≠ j ∧ (K ∩ (P k).carrier).Nonempty) with hT0
  have hρw : 0 ≤ 2 * kRho * w := by positivity
  have hcount : kTau * (132 / 1000 * kRho ^ 2 * s) ≤ (T0.card + 2) * (2 * kRho * w) := by
    have h1 : ENNReal.ofReal (kTau * (132 / 1000 * kRho ^ 2 * s)) ≤
        volume (K ∩ ⋃ k ∈ nbhdFam P i j, (P k).carrier) := by
      rw [ENNReal.ofReal_mul (by norm_num [kTau])]
      exact le_trans (by gcongr) hcov
    have h2 : K ∩ ⋃ k ∈ nbhdFam P i j, (P k).carrier ⊆
        ⋃ k ∈ insert i (insert j T0), K ∩ (P k).carrier := by
      rintro x ⟨hxK, hx⟩
      simp only [mem_iUnion] at hx ⊢
      obtain ⟨k, hk, hxk⟩ := hx
      refine ⟨k, ?_, hxK, hxk⟩
      by_cases hki : k = i
      · simp [hki]
      by_cases hkj : k = j
      · simp [hkj]
      simp only [Finset.mem_insert, hki, hkj, false_or]
      simp only [T0, Nf, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hk, hki, hkj, x, hxK, hxk⟩
    have h3 : volume (⋃ k ∈ insert i (insert j T0), K ∩ (P k).carrier) ≤
        ENNReal.ofReal ((T0.card + 2) * (2 * kRho * w)) := by
      refine (measure_biUnion_finset_le _ _).trans ?_
      refine (Finset.sum_le_sum fun k _ => hstrip k).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hc1 : (insert i (insert j T0)).card ≤ T0.card + 2 :=
        (Finset.card_insert_le i (insert j T0)).trans
          (Nat.succ_le_succ (Finset.card_insert_le j T0))
      have : ((insert i (insert j T0)).card : ℝ) ≤ T0.card + 2 := by exact_mod_cast hc1
      exact mul_le_mul_of_nonneg_right this hρw
    have := (h1.trans (measure_mono h2)).trans h3
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
  -- lower bound on the number of planks
  have hN0 : kTau * kRho * s / 16 ≤ T0.card * w := by
    have e1 : kTau * (132 / 1000 * kRho ^ 2 * s) = kRho * (kTau * (132 / 1000) * kRho * s) := by
      ring
    have e2 : (T0.card + 2) * (2 * kRho * w) = kRho * (2 * (T0.card + 2) * w) := by ring
    rw [e1, e2] at hcount
    have h := le_of_mul_le_mul_left hcount hρ
    norm_num [kTau, kA] at h hsA ⊢
    nlinarith
  -- data attached to each plank
  have hdata : ∀ k ∈ T0, ∃ p ν : Plane, ∃ o : ℝ, p ∈ chord (P i) ∪ chord (P j) ∧
      (ν = (P k).n ∨ ν = -(P k).n) ∧ inner ℝ p ν = o ∧
      ∀ x : Plane, o ≤ inner ℝ x ν → inner ℝ x ν ≤ o + w / 2 → x ∈ (P k).carrier := by
    intro k hk
    obtain ⟨-, -, -, y, hyK, hyk⟩ := Finset.mem_filter.1 hk
    obtain ⟨p, hp, hpy⟩ := exists_chord_of_mem_hull hcP hcQ (P k).n hyK
    obtain ⟨ν, o, hν, hpo, hb⟩ := exists_band_of_mem_carrier (hw k) hyk hpy
    exact ⟨p, ν, o, hp, hν, hpo, hb⟩
  choose! p ν o hp hνk hpo hband using hdata
  set a := min 1 (3 * s) with ha_def
  have ha0 : 0 < a := lt_min one_pos (by linarith)
  have ha1 : a ≤ 1 := min_le_left _ _
  have ha3 : a ≤ 3 * s := min_le_right _ _
  have hνn : ∀ k ∈ T0, ‖ν k‖ = 1 := fun k hk => by
    rcases hνk k hk with h | h <;> rw [h]
    · exact (P k).norm_n
    · rw [norm_neg]; exact (P k).norm_n
  have hsinS : ∀ k ∈ T0, |inner ℝ (J (P i).n) (ν k)| ≤ a ∧
      |inner ℝ (J (P j).n) (ν k)| ≤ a := by
    intro k hk
    have hkN : k ∈ nbhdFam P i j := by
      have := (Finset.mem_filter.1 hk).1
      simpa [Nf] using this
    have hb := sin_bound_of_mem_nbhdFam P hkN
    have e : ∀ S : ι, |inner ℝ (J (P S).n) (ν k)| = |inner ℝ (J (P S).n) (P k).n| := by
      intro S
      rcases hνk k hk with h | h <;> rw [h]
      rw [inner_neg_right, abs_neg]
    rw [e i, e j]
    exact ⟨le_min (Plank.sin_ang_le_one _ _) hb.1, le_min (Plank.sin_ang_le_one _ _) hb.2⟩
  have hC : 2 * w ≤ a * kRho := by
    rw [ha_def, min_mul_of_nonneg _ _ hρ.le]
    refine le_min (by linarith) ?_
    norm_num [kA] at hsA; nlinarith
  -- conclusion along one arm
  have hfinish : ∀ S, (S = i ∨ S = j) → ∀ T ⊆ T0, T0.card ≤ 2 * T.card →
      (∀ k ∈ T, p k ∈ chord (P S)) →
      ENNReal.ofReal (kGamma * kRho * w) ≤
        volume (denseRegion P kDelta ∩ ((P i).carrier ∪ (P j).carrier) ∩
          closedBall 0 (5 * kRho)) := by
    intro S hS T hT hcardT hpS
    have hSmid : |(P S).mid| ≤ kRho := by
      unfold IsCentral at hcen; unfold IsDeep at hdeep
      rcases hS with rfl | rfl <;> linarith
    have hSnot : S ∉ T := fun h => by
      have := (Finset.mem_filter.1 (hT h)).2
      rcases hS with rfl | rfl
      · exact this.1 rfl
      · exact this.2.1 rfl
    have harm := arm_pays P hw0 hw hSmid T hSnot p ν o hpS (fun k hk => hνn k (hT hk))
      (fun k hk => hpo k (hT hk)) (fun k hk => hband k (hT hk)) ha0 ha1
      (fun k hk => by
        rcases hS with rfl | rfl
        · exact (hsinS k (hT hk)).1
        · exact (hsinS k (hT hk)).2) hC
    refine le_trans ?_ (harm.trans (measure_mono ?_))
    · apply ENNReal.ofReal_le_ofReal
      have hT2 : kTau * kRho * s / 32 ≤ T.card * w := by
        have : (T0.card : ℝ) ≤ 2 * T.card := by exact_mod_cast hcardT
        nlinarith
      have hm : 2e-9 * kRho ≤ min (T.card * w / (192 * a)) (2 * kRho / 3) := by
        refine le_min ?_ (by linarith)
        rw [le_div_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_left ha3 hρ.le
        norm_num [kTau] at hT2 ⊢
        nlinarith
      have := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ w / 2)
      norm_num [kGamma] at this ⊢
      linarith
    · rintro x ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rcases hS with rfl | rfl
      · exact Or.inl h2
      · exact Or.inr h2
  set Ti := T0.filter (fun k => p k ∈ chord (P i)) with hTi
  set Tj := T0.filter (fun k => p k ∉ chord (P i)) with hTj
  have hcard : Ti.card + Tj.card = T0.card := Finset.card_filter_add_card_filter_not _
  rcases le_total Tj.card Ti.card with h | h
  · exact hfinish i (Or.inl rfl) Ti (Finset.filter_subset _ _) (by omega)
      (fun k hk => (Finset.mem_filter.1 hk).2)
  · refine hfinish j (Or.inr rfl) Tj (Finset.filter_subset _ _) (by omega) (fun k hk => ?_)
    have := Finset.mem_filter.1 hk
    rcases hp k this.1 with h' | h'
    · exact absurd h' this.2
    · exact h'

end Annulus

end
