module

public import RequestProject.Overlap.Hull
public import RequestProject.Overlap.DenseDisk
public import RequestProject.Overlap.OneDim

/-!
# Dense area along one arm

If many planks `R_k` contain half-width bands along lines `ℓ'_k` crossing the center line of
`S` at points `p_k` of its chord, with small angle to `ℓ_S`, then a definite amount of the dense
region lies in `S` near its center line.
-/

@[expose] public section

open MeasureTheory Set Metric Real
open scoped ENNReal

noncomputable section

namespace Annulus

variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
/-- Dense area along one arm (step 5 of the price estimate). -/
theorem arm_pays (P : ι → Plank) {w : ℝ} (hw0 : 0 < w) (hw : EqualWidth P w)
    {S : ι} (hSmid : |(P S).mid| ≤ kRho) (T : Finset ι) (hST : S ∉ T)
    (p ν : ι → Plane) (o : ι → ℝ) (hp : ∀ k ∈ T, p k ∈ chord (P S))
    (hν : ∀ k ∈ T, ‖ν k‖ = 1) (hpo : ∀ k ∈ T, inner ℝ (p k) (ν k) = o k)
    (hband : ∀ k ∈ T, ∀ x : Plane, o k ≤ inner ℝ x (ν k) → inner ℝ x (ν k) ≤ o k + w / 2 →
      x ∈ (P k).carrier)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hsin : ∀ k ∈ T, |inner ℝ (J (P S).n) (ν k)| ≤ a)
    (hC : 2 * w ≤ a * kRho) :
    ENNReal.ofReal (w / 2 * min (T.card * w / (192 * a)) (2 * kRho / 3)) ≤
      volume (denseRegion P kDelta ∩ (P S).carrier ∩ closedBall 0 (5 * kRho)) := by
  classical
  set n := (P S).n with hn_def
  set m := (P S).mid with hm_def
  set e := J n with he_def
  have hρ := kRho_pos
  have haρ : a * kRho ≤ kRho := by nlinarith
  have hn : ‖n‖ = 1 := (P S).norm_n
  have he : ‖e‖ = 1 := by rw [he_def, norm_J, hn]
  have hnn : inner ℝ n n = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hne : inner ℝ n e = (0 : ℝ) := inner_self_J n
  have hen : inner ℝ e n = (0 : ℝ) := inner_J_self n
  set u : ι → ℝ := fun k => a * inner ℝ (p k) e with hu_def
  obtain ⟨V, r, hVT, hdisj, hr, hgood, hsum⟩ :=
    one_dim_cover (κ := 12) (by norm_num) hw0 hC T u
  set z : ℝ → Plane := fun t => m • n + t • e with hz_def
  have hzline : ∀ t, z t ∈ (P S).centerLine := fun t => by
    show inner ℝ (m • n + t • e) n = m
    simp only [inner_add_left, inner_smul_left, hnn, hen, RCLike.conj_to_real]; ring
  have hznorm : ∀ t, ‖z t‖ ^ 2 = m ^ 2 + t ^ 2 := fun t => by
    rw [Plank.norm_sq_of_mem_centerLine (hzline t), ← hm_def, ← hn_def, ← he_def]
    simp only [z, inner_add_left, inner_smul_left, hne, hee, RCLike.conj_to_real]
    ring
  -- distance from `z t` to the line `ℓ'_k`
  have hdist : ∀ k ∈ T, ∀ t, |inner ℝ (z t) (ν k) - o k| ≤ |a * t - u k| := by
    intro k hk t
    have hpk := hp k hk
    have hpl : p k = m • n + inner ℝ (p k) e • e := Plank.eq_of_mem_centerLine hpk.1
    have : inner ℝ (z t) (ν k) - o k = (t - inner ℝ (p k) e) * inner ℝ e (ν k) := by
      rw [← hpo k hk, ← inner_sub_left]
      conv_lhs => rw [hpl]
      simp only [z]
      rw [show m • n + t • e - (m • n + inner ℝ (p k) e • e) = (t - inner ℝ (p k) e) • e by
        module, inner_smul_left, RCLike.conj_to_real]
    rw [this, abs_mul]
    have h1 : |inner ℝ e (ν k)| ≤ a := hsin k hk
    calc |t - inner ℝ (p k) e| * |inner ℝ e (ν k)| ≤ |t - inner ℝ (p k) e| * a := by gcongr
      _ = |a * t - u k| := by
        simp only [u]; rw [← mul_sub, abs_mul, abs_of_pos ha0]; ring
  -- disks around `z t` stay in `D`
  have hdisk : ∀ t, |t| ≤ 2 * kRho → ∀ R, R ≤ 4 * kRho → ball (z t) R ⊆ unitDisk := by
    intro t ht R hR y hy
    have h1 : ‖z t‖ ≤ 3 * kRho := by
      have h2 : ‖z t‖ ^ 2 ≤ (3 * kRho) ^ 2 := by
        rw [hznorm]
        have : m ^ 2 ≤ kRho ^ 2 := by rw [← sq_abs]; gcongr
        have : t ^ 2 ≤ (2 * kRho) ^ 2 := by rw [← sq_abs]; gcongr
        nlinarith
      exact (sq_le_sq₀ (norm_nonneg _) (by linarith)).1 h2
    have h3 : ‖y - z t‖ < R := by rw [← dist_eq_norm]; exact mem_ball.1 hy
    simp only [unitDisk, mem_closedBall, dist_zero_right]
    have := norm_le_insert' y (z t)
    have : ‖y‖ ≤ ‖z t‖ + ‖y - z t‖ := by
      calc ‖y‖ = ‖z t + (y - z t)‖ := by rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have : kRho = 1 / 12 := rfl
    linarith
  -- good points give dense disks
  have hball : ∀ t, |t| ≤ 2 * kRho → ((∃ i ∈ T, |a * t - u i| ≤ w / 8) ∨
      ∃ s, 2 * w ≤ s ∧ s ≤ 2 * (a * kRho) ∧ 12 * s / w ≤ (nearCount T u (a * t) s : ℝ)) →
      ball (z t) (w / 2) ⊆ denseRegion P kDelta := by
    intro t ht hgd
    rcases hgd with ⟨i, hi, hti⟩ | ⟨s, hs1, hs2, hs3⟩
    · have hSi : S ≠ i := fun h => hST (h ▸ hi)
      have hdd := isDenseDisk_pair P hw0 hw hSi (hzline t) (hν i hi) (hband i hi)
        ((hdist i hi t).trans hti) (hdisk t ht _ (by linarith))
      intro y hy
      simp only [denseRegion, mem_iUnion]
      exact ⟨z t, w / 2, hdd, hy⟩
    · set T' := T.filter fun j => |a * t - u j| ≤ s
      have hdd := isDenseDisk_cluster P hw0 (z := z t) hs1 T' ν
        (fun j hj => hν j (Finset.mem_of_mem_filter _ hj)) o
        (fun j hj => hband j (Finset.mem_of_mem_filter _ hj))
        (fun j hj => (hdist j (Finset.mem_of_mem_filter _ hj) t).trans
          (Finset.mem_filter.1 hj).2) hs3 (hdisk t ht _ (by nlinarith))
      intro y hy
      simp only [denseRegion, mem_iUnion]
      exact ⟨z t, 2 * s, hdd, ball_subset_ball (by linarith) hy⟩
  -- the parameter set
  set G : ι → Set ℝ := fun j => Icc ((u j - r j) / a) ((u j + r j) / a) with hG_def
  have hGt : ∀ j ∈ V, ∀ t ∈ G j, |t| ≤ 2 * kRho ∧ ((∃ i ∈ T, |a * t - u i| ≤ w / 8) ∨
      ∃ s, 2 * w ≤ s ∧ s ≤ 2 * (a * kRho) ∧ 12 * s / w ≤ (nearCount T u (a * t) s : ℝ)) := by
    intro j hj t ht
    have hat : a * t ∈ Icc (u j - r j) (u j + r j) := by
      obtain ⟨h1, h2⟩ := ht
      rw [div_le_iff₀ ha0] at h1; rw [le_div_iff₀ ha0] at h2
      exact ⟨by linarith, by linarith⟩
    refine ⟨?_, hgood j hj _ hat⟩
    have hjT := hVT hj
    have hpj := (mem_chord.1 (hp j hjT)).2
    have hue : |inner ℝ (p j) e| ≤ kRho := by
      have := abs_real_inner_le_norm (p j) e
      rw [he, mul_one] at this; linarith
    have hu : |u j| ≤ a * kRho := by
      simp only [u]; rw [abs_mul, abs_of_pos ha0]; gcongr
    have hrj := hr j hj
    have : |a * t| ≤ 2 * (a * kRho) := by
      rw [abs_le] at hu ⊢; constructor <;> linarith [hat.1, hat.2]
    rw [abs_mul, abs_of_pos ha0] at this
    nlinarith
  -- points of the region
  have hmem : ∀ q : ℝ × ℝ, q.1 ∈ Icc (-(w / 4)) (w / 4) → q.2 ∈ ⋃ j ∈ V, G j →
      frame (m • n) n q ∈ denseRegion P kDelta ∩ (P S).carrier ∩ closedBall 0 (5 * kRho) := by
    rintro ⟨v, t⟩ hv ht
    simp only [mem_iUnion] at ht
    obtain ⟨j, hj, ht⟩ := ht
    obtain ⟨htb, hgd⟩ := hGt j hj t ht
    have hq : frame (m • n) n (v, t) = z t + v • n := by
      simp only [frame, z, ← he_def]; abel
    have hvn : ‖v • n‖ = |v| := by rw [norm_smul, hn, mul_one, Real.norm_eq_abs]
    have hv' : |v| ≤ w / 4 := abs_le.2 ⟨hv.1, hv.2⟩
    rw [hq]
    refine ⟨⟨hball t htb hgd ?_, ?_⟩, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hvn]; linarith
    · rw [Plank.mem_carrier_iff, hw S]
      have : inner ℝ (z t + v • n) n - m = v := by
        rw [inner_add_left, Plank.mem_centerLine.1 (hzline t), inner_smul_left, hnn]
        simp [hm_def]
      rw [this]; linarith
    · rw [mem_closedBall, dist_zero_right]
      have h1 : ‖z t‖ ≤ 3 * kRho := by
        have h2 : ‖z t‖ ^ 2 ≤ (3 * kRho) ^ 2 := by
          rw [hznorm]
          have : m ^ 2 ≤ kRho ^ 2 := by rw [← sq_abs]; gcongr
          have : t ^ 2 ≤ (2 * kRho) ^ 2 := by rw [← sq_abs]; gcongr
          nlinarith
        exact (sq_le_sq₀ (norm_nonneg _) (by linarith)).1 h2
      calc ‖z t + v • n‖ ≤ ‖z t‖ + ‖v • n‖ := norm_add_le _ _
        _ ≤ 5 * kRho := by
          have : a * kRho ≤ kRho := by nlinarith
          rw [hvn]; linarith
  -- volume computation
  have hGdisj : (↑V : Set ι).PairwiseDisjoint G := by
    intro i hi j hj hij
    rw [Function.onFun, Set.disjoint_left]
    intro t hti htj
    have key := hdisj hi hj hij
    rw [Function.onFun, Set.disjoint_left] at key
    have hat : ∀ k, t ∈ G k → a * t ∈ Icc (u k - r k) (u k + r k) := by
      intro k ht
      obtain ⟨h1, h2⟩ := ht
      rw [div_le_iff₀ ha0] at h1; rw [le_div_iff₀ ha0] at h2
      exact ⟨by linarith, by linarith⟩
    exact key (hat i hti) (hat j htj)
  have hvolG : volume (⋃ j ∈ V, G j) = ENNReal.ofReal (∑ j ∈ V, 2 * r j / a) := by
    rw [measure_biUnion_finset hGdisj (fun j _ => measurableSet_Icc),
      ENNReal.ofReal_sum_of_nonneg (fun j hj => by have := (hr j hj).1; positivity)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.volume_Icc]; congr 1; ring
  rw [volume_eq_frame_preimage (m • n) n hn]
  calc ENNReal.ofReal (w / 2 * min (T.card * w / (192 * a)) (2 * kRho / 3))
      ≤ ENNReal.ofReal (w / 2) * ENNReal.ofReal (∑ j ∈ V, 2 * r j / a) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        gcongr
        rw [← Finset.sum_div, le_div_iff₀ ha0, min_mul_of_nonneg _ _ ha0.le]
        convert hsum using 2
        · field_simp; ring
        · field_simp
    _ = volume (Icc (-(w / 4)) (w / 4) ×ˢ ⋃ j ∈ V, G j) := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, hvolG]
        congr 2; ring
    _ ≤ _ := measure_mono fun q hq => hmem q hq.1 hq.2

end Annulus

end
