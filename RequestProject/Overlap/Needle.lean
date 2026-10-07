module

public import RequestProject.Overlap.Cells

/-!
# Needle lemma for small cells

A cell which meets `rD` and is contained in the small disk `B(0, 0.032 ρ)` is bounded by
central survivors only.  These are nearly parallel, so in coordinates along a reference
direction the upper and lower constraints must cross within the disk `B(0, 0.05 ρ)`; two
crossing constraints form a surviving candidate pair `(P_k, P_l)`, and the whole cell lies
within `0.07 ρ sin ang(P_k, P_l)` of `ℓ_k`.
-/

@[expose] public section

open MeasureTheory Set Metric Real
open scoped ENNReal

noncomputable section

namespace Annulus

variable {ι : Type*}

open Classical in
/-- Outward normal of the constraint of plank `k` for the cell with sign pattern `A`. -/
def outN (P : ι → Plank) (A : Finset ι) (k : ι) : Plane := if k ∈ A then (P k).n else -(P k).n

open Classical in
/-- Offset of the constraint of plank `k` for the cell with sign pattern `A`. -/
def outC (P : ι → Plank) (A : Finset ι) (k : ι) : ℝ := if k ∈ A then (P k).a else -(P k).b

lemma norm_outN (P : ι → Plank) (A : Finset ι) (k : ι) : ‖outN P A k‖ = 1 := by
  unfold outN; split_ifs <;> simp [(P k).norm_n]

lemma side_iff (P : ι → Plank) (A : Finset ι) (k : ι) (x : Plane) :
    ((k ∈ A → inner ℝ x (P k).n < (P k).a) ∧ (k ∉ A → (P k).b < inner ℝ x (P k).n)) ↔
      inner ℝ x (outN P A k) < outC P A k := by
  unfold outN outC
  by_cases hk : k ∈ A
  · simp [hk]
  · simp [hk, inner_neg_right]

lemma dist_eq_of_side (P : ι → Plank) (A : Finset ι) (k : ι) {x : Plane}
    (hx : inner ℝ x (outN P A k) < outC P A k) :
    |inner ℝ x (P k).n - (P k).mid| = (P k).width / 2 + (outC P A k - inner ℝ x (outN P A k)) := by
  unfold outN outC at *
  simp only [Plank.mid, Plank.width] at *
  by_cases hk : k ∈ A
  · simp only [hk, if_true] at hx ⊢
    rw [abs_of_neg (by linarith [(P k).a_le_b])]; ring
  · simp only [hk, if_false, inner_neg_right] at hx ⊢
    rw [abs_of_pos (by linarith [(P k).a_le_b])]; ring

lemma abs_inner_J_outN (P : ι → Plank) (A : Finset ι) (k : ι) (u : Plane) :
    |inner ℝ u (outN P A k)| = |inner ℝ u (P k).n| := by
  unfold outN; split_ifs <;> simp [inner_neg_right]

lemma abs_inner_J_outN_outN (P : ι → Plank) (A : Finset ι) (k l : ι) :
    |inner ℝ (J (outN P A k)) (outN P A l)| = |inner ℝ (J (P k).n) (P l).n| := by
  unfold outN; split_ifs <;> simp [inner_neg_right, inner_neg_left, J_neg]

variable [Fintype ι]

omit [Fintype ι] in
/-- A point of the small disk satisfying the constraints of the central survivors belongs to
the cell. -/
lemma mem_cell_of_central (P : ι → Plank) {w r : ℝ} (hw : EqualWidth P w)
    (hwρ : w ≤ kRho / 1000) (hrρ : r ≤ kRho / 2000) {S A : Finset ι} {p0 : Plane}
    (hp0 : p0 ∈ cell P S A) (hp0r : ‖p0‖ ≤ r) {x : Plane} (hx : ‖x‖ < 5 / 100 * kRho)
    (hxc : ∀ k ∈ S, IsCentral (P k) → inner ℝ x (outN P A k) < outC P A k) :
    x ∈ cell P S A := by
  have hρ := kRho_pos
  refine ⟨by have : kRho < 1 := by norm_num [kRho]
             linarith, fun k hk => (side_iff P A k x).2 ?_⟩
  by_cases hc : IsCentral (P k)
  · exact hxc k hk hc
  have hmid : 7 / 100 * kRho < |(P k).mid| := by unfold IsCentral at hc; push_neg at hc; exact hc
  have hp := (side_iff P A k p0).1 (hp0.2 k hk)
  have h1 : |inner ℝ p0 (P k).n| ≤ r := (abs_inner_le_norm_of_unit (P k).norm_n p0).trans hp0r
  have h2 : |inner ℝ x (P k).n| < 5 / 100 * kRho :=
    lt_of_le_of_lt (abs_inner_le_norm_of_unit (P k).norm_n x) hx
  have hwk := hw k
  unfold outN outC at hp ⊢
  simp only [Plank.mid, Plank.width] at hmid hwk
  rw [abs_lt] at h2
  rw [abs_le] at h1
  by_cases hkA : k ∈ A
  · simp only [hkA, if_true] at hp ⊢
    rcases lt_abs.1 hmid with h | h <;> linarith [(P k).a_le_b]
  · simp only [hkA, if_false, inner_neg_right] at hp ⊢
    rcases lt_abs.1 hmid with h | h <;> linarith [(P k).a_le_b]

omit [Fintype ι] in
set_option maxHeartbeats 4000000 in
/-- The needle lemma, relative to a reference direction `n₀` almost parallel to all central
survivors. -/
theorem needle_aux (P : ι → Plank) {w r : ℝ} (hw0 : 0 < w) (hw : EqualWidth P w)
    (hsep : AngleSep P w) (hwρ : w ≤ kRho / 1000) (hr : 0 < r) (hrρ : r ≤ kRho / 2000)
    {S A : Finset ι} {n0 : Plane} (hn0 : ‖n0‖ = 1)
    (hpar : ∀ k ∈ S, IsCentral (P k) → |inner ℝ (J n0) (P k).n| < 1 / 5)
    {p0 : Plane} (hp0 : p0 ∈ cell P S A) (hp0r : ‖p0‖ ≤ r)
    (hsub : cell P S A ⊆ closedBall 0 (32 / 1000 * kRho)) :
    ∃ k ∈ S, ∃ l ∈ S, IsCandidate P k l ∧
      ∀ x ∈ cell P S A, |inner ℝ x (P k).n - (P k).mid| ≤
        7 / 100 * kRho * |inner ℝ (J (P k).n) (P l).n| := by
  classical
  have hρ := kRho_pos
  set e := J n0 with he_def
  have he : ‖e‖ = 1 := by rw [he_def, norm_J, hn0]
  set m := outN P A with hm_def
  set c := outC P A with hc_def
  set α : ι → ℝ := fun k => inner ℝ e (m k) with hα_def
  set β : ι → ℝ := fun k => inner ℝ n0 (m k) with hβ_def
  have hcoord : ∀ x k, inner ℝ x (m k) = inner ℝ x n0 * β k + inner ℝ x e * α k :=
    fun x k => inner_decomp hn0 x (m k)
  have hαβ : ∀ k ∈ S, IsCentral (P k) → |α k| < 1 / 5 ∧ 979 / 1000 < |β k| ∧ |β k| ≤ 1 := by
    intro k hk hc
    have h1 : |α k| < 1 / 5 := by
      simp only [α, m]; rw [abs_inner_J_outN]; exact hpar k hk hc
    have h2 := inner_sq_add_inner_J_sq n0 (m k)
    rw [hn0, norm_outN] at h2
    have h3 : β k ^ 2 = 1 - α k ^ 2 := by simp only [α, β]; linarith
    have h4 : α k ^ 2 < 1 / 25 := by
      have := sq_abs (α k); nlinarith [abs_nonneg (α k)]
    refine ⟨h1, ?_, ?_⟩
    · have : (979 / 1000) ^ 2 < |β k| ^ 2 := by rw [sq_abs]; nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) this
    · have : |β k| ^ 2 ≤ 1 := by rw [sq_abs]; nlinarith [sq_nonneg (α k)]
      nlinarith [abs_nonneg (β k)]
  set Up := S.filter fun k => IsCentral (P k) ∧ 0 < β k with hUp_def
  set Lo := S.filter fun k => IsCentral (P k) ∧ β k < 0 with hLo_def
  set U : ι → ℝ → ℝ := fun k t => (c k - t * α k) / β k with hU_def
  have hUp : ∀ k ∈ Up, ∀ x, inner ℝ x (m k) < c k ↔ inner ℝ x n0 < U k (inner ℝ x e) := by
    intro k hk x
    have hb := (Finset.mem_filter.1 hk).2.2
    rw [hcoord, lt_div_iff₀ hb]; constructor <;> intro h <;> linarith
  have hLo : ∀ k ∈ Lo, ∀ x, inner ℝ x (m k) < c k ↔ U k (inner ℝ x e) < inner ℝ x n0 := by
    intro k hk x
    have hb := (Finset.mem_filter.1 hk).2.2
    rw [hcoord, div_lt_iff_of_neg hb]; constructor <;> intro h <;> linarith
  have hcentral : ∀ k ∈ S, IsCentral (P k) → k ∈ Up ∨ k ∈ Lo := by
    intro k hk hc
    have := (hαβ k hk hc).2.1
    rcases lt_trichotomy (β k) 0 with h | h | h
    · right; exact Finset.mem_filter.2 ⟨hk, hc, h⟩
    · rw [h, abs_zero] at this; norm_num at this
    · left; exact Finset.mem_filter.2 ⟨hk, hc, h⟩
  have hUslope : ∀ k ∈ S, IsCentral (P k) → ∀ t t', |U k t' - U k t| ≤ |t' - t| / 4 := by
    intro k hk hc t t'
    obtain ⟨h1, h2, -⟩ := hαβ k hk hc
    have hb : β k ≠ 0 := by intro h; rw [h, abs_zero] at h2; norm_num at h2
    have : U k t' - U k t = -(t' - t) * (α k / β k) := by simp only [U]; field_simp; ring
    rw [this, abs_mul, abs_neg]
    have : |α k / β k| ≤ 1 / 4 := by
      rw [abs_div, div_le_iff₀ (by linarith)]; linarith
    nlinarith [abs_nonneg (t' - t)]
  -- the base point
  set t0 := inner ℝ p0 e with ht0_def
  set y0 := inner ℝ p0 n0 with hy0_def
  have hp0side : ∀ k ∈ S, inner ℝ p0 (m k) < c k :=
    fun k hk => (side_iff P A k p0).1 (hp0.2 k hk)
  have ht0 : |t0| ≤ r := (abs_inner_le_norm_of_unit he p0).trans hp0r
  have hy0 : |y0| ≤ r := (abs_inner_le_norm_of_unit hn0 p0).trans hp0r
  set R0 := 32 / 1000 * kRho with hR0_def
  set D := R0 + 2 * r with hD_def
  have hD : 0 < D := by positivity
  set t1 := t0 + D with ht1_def
  have hUpp : ∀ k ∈ Up, y0 < U k t0 ∧ y0 - D / 4 < U k t1 := by
    intro k hk
    have h1 := (hUp k hk p0).1 (hp0side k (Finset.mem_of_mem_filter _ hk))
    have hkf := Finset.mem_filter.1 hk
    have h2 := hUslope k hkf.1 hkf.2.1 t0 t1
    rw [show t1 - t0 = D by ring, abs_of_pos hD] at h2
    exact ⟨h1, by rw [abs_le] at h2; linarith [h2.1]⟩
  have hLop : ∀ l ∈ Lo, U l t0 < y0 ∧ U l t1 < y0 + D / 4 := by
    intro l hl
    have h1 := (hLo l hl p0).1 (hp0side l (Finset.mem_of_mem_filter _ hl))
    have hlf := Finset.mem_filter.1 hl
    have h2 := hUslope l hlf.1 hlf.2.1 t0 t1
    rw [show t1 - t0 = D by ring, abs_of_pos hD] at h2
    exact ⟨h1, by rw [abs_le] at h2; linarith [h2.2]⟩
  -- an upper and a lower constraint cross before `t₁`
  have hkey : ∃ k ∈ Up, ∃ l ∈ Lo, U k t1 ≤ U l t1 := by
    by_contra hcon
    push_neg at hcon
    set Ls := insert (y0 - D / 4) (Lo.image fun l => U l t1) with hLs_def
    set Us := insert (y0 + D / 4) (Up.image fun k => U k t1) with hUs_def
    have hLs : Ls.Nonempty := Finset.insert_nonempty _ _
    have hUs : Us.Nonempty := Finset.insert_nonempty _ _
    have hsep' : ∀ a ∈ Ls, ∀ b ∈ Us, a < b := by
      intro a ha b hb
      rcases Finset.mem_insert.1 ha with rfl | ha <;> rcases Finset.mem_insert.1 hb with rfl | hb
      · linarith
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hb
        exact (hUpp k hk).2
      · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 ha
        exact (hLop l hl).2
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hb
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 ha
        exact hcon k hk l hl
    have hlt : Ls.max' hLs < Us.min' hUs :=
      hsep' _ (Finset.max'_mem _ _) _ (Finset.min'_mem _ _)
    set ym := (Ls.max' hLs + Us.min' hUs) / 2 with hym_def
    have hym1 : ∀ a ∈ Ls, a < ym := fun a ha => by
      have := Finset.le_max' Ls a ha; linarith
    have hym2 : ∀ b ∈ Us, ym < b := fun b hb => by
      have := Finset.min'_le Us b hb; linarith
    have hyma : y0 - D / 4 < ym := hym1 _ (Finset.mem_insert_self _ _)
    have hymb : ym < y0 + D / 4 := hym2 _ (Finset.mem_insert_self _ _)
    set q := ym • n0 + t1 • e with hq_def
    have hnn : inner ℝ n0 n0 = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hn0]; norm_num
    have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he]; norm_num
    have hen0 : inner ℝ e n0 = (0 : ℝ) := by rw [he_def]; exact inner_J_self n0
    have hn0e : inner ℝ n0 e = (0 : ℝ) := by rw [he_def]; exact inner_self_J n0
    have hqn0 : inner ℝ q n0 = ym := by
      simp only [q, inner_add_left, inner_smul_left, hnn, hen0, RCLike.conj_to_real]; ring
    have hqe : inner ℝ q e = t1 := by
      simp only [q, inner_add_left, inner_smul_left, hee, hn0e, RCLike.conj_to_real]; ring
    have hqnorm : ‖q‖ ≤ |ym| + |t1| := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, hn0, he, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one]
    have hym_abs : |ym| ≤ r + D / 4 := by
      rw [abs_le] at hy0 ⊢; constructor <;> linarith
    have ht1_abs : |t1| ≤ r + D := by
      rw [abs_le] at ht0 ⊢; constructor <;> linarith
    have hqcell : q ∈ cell P S A := by
      refine mem_cell_of_central P hw hwρ hrρ hp0 hp0r ?_ ?_
      · simp only [hD_def, hR0_def] at hym_abs ht1_abs; linarith
      · intro k hk hc
        rcases hcentral k hk hc with hk' | hk'
        · rw [hUp k hk' q, hqn0, hqe]
          exact hym2 _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hk'))
        · rw [hLo k hk' q, hqn0, hqe]
          exact hym1 _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hk'))
    have h1 := mem_closedBall_zero_iff.1 (hsub hqcell)
    have h2 : |t1| ≤ ‖q‖ := by rw [← hqe]; exact abs_inner_le_norm_of_unit he q
    have h3 : R0 + r ≤ t1 := by rw [abs_le] at ht0; linarith [ht0.1]
    have h4 : t1 ≤ |t1| := le_abs_self _
    linarith
  obtain ⟨k, hk, l, hl, hkl⟩ := hkey
  obtain ⟨hkS, hkc, hbk⟩ := Finset.mem_filter.1 hk
  obtain ⟨hlS, hlc, hbl⟩ := Finset.mem_filter.1 hl
  obtain ⟨hαk, hβk, hβk1⟩ := hαβ k hkS hkc
  obtain ⟨hαl, hβl, hβl1⟩ := hαβ l hlS hlc
  rw [abs_of_pos hbk] at hβk hβk1
  rw [abs_of_neg hbl] at hβl hβl1
  have hbk0 : β k ≠ 0 := hbk.ne'
  have hbl0 : β l ≠ 0 := hbl.ne
  set g := α l / β l - α k / β k with hg_def
  have hG : ∀ t, U k t - U l t = (U k t0 - U l t0) + g * (t - t0) := by
    intro t; simp only [U, g]; field_simp; ring
  have hG0 : 0 < U k t0 - U l t0 := by linarith [(hUpp k hk).1, (hLop l hl).1]
  have hG1 : U k t0 - U l t0 ≤ -g * D := by
    have := hG t1; rw [show t1 - t0 = D by ring] at this; linarith
  have hg : g < 0 := by
    by_contra h; push_neg at h; nlinarith
  -- `g` and the sine of the angle
  set s := |inner ℝ (J (P k).n) (P l).n| with hs_def
  have hnum : inner ℝ (J (m k)) (m l) = β k * α l - α k * β l := by
    rw [inner_J_frame hn0]
    simp only [α, β, he_def, real_inner_comm]
  have hgeq : g = (β k * α l - α k * β l) / (β k * β l) := by
    rw [hg_def, div_sub_div _ _ hbl0 hbk0]; ring
  have hsnum : |β k * α l - α k * β l| = s := by
    rw [← hnum]; exact abs_inner_J_outN_outN P A k l
  have hgs : -g ≤ s / (958 / 1000) := by
    have hbb : 958 / 1000 ≤ -(β k * β l) := by nlinarith
    rw [hgeq, ← div_neg, div_le_div_iff₀ (by linarith) (by norm_num), ← hsnum]
    have := le_abs_self (β k * α l - α k * β l)
    have := abs_nonneg (β k * α l - α k * β l)
    nlinarith
  have hs0 : 0 < s := by
    rw [← hsnum]; apply abs_pos.2
    intro h; rw [hgeq, h, zero_div] at hg; exact lt_irrefl 0 hg
  have hs1 : s ≤ 1 := Plank.sin_ang_le_one _ _
  have hang : (P k).ang (P l) ≠ 0 := (Plank.ang_ne_zero_iff _ _).2 (by
    intro h; rw [hs_def, h, abs_zero] at hs0; exact lt_irrefl 0 hs0)
  -- `w` is tiny compared with `ρ s`
  have hws : w ≤ 2 * kRho * s / 1e13 := by
    have hwsep := hsep k l hang
    have h1 := two_div_pi_mul_le_sin (Plank.ang_nonneg (P k) (P l)) (Plank.ang_le _ _)
    rw [Plank.sin_ang] at h1
    have h2 : 1 / 2 ≤ 2 / π := by rw [le_div_iff₀ pi_pos]; linarith [pi_le_four]
    have h3 : (P k).ang (P l) / 2 ≤ s := by nlinarith [Plank.ang_nonneg (P k) (P l)]
    rw [le_div_iff₀ (by norm_num)]
    norm_num [kA] at hwsep
    nlinarith
  -- the cell lies close to `ℓ_k`
  have hdist : ∀ x ∈ cell P S A, |inner ℝ x (P k).n - (P k).mid| ≤ 7 / 100 * kRho * s := by
    intro x hx
    set t := inner ℝ x e with ht_def
    set y := inner ℝ x n0 with hy_def
    have hxk : inner ℝ x (m k) < c k := (side_iff P A k x).1 (hx.2 k hkS)
    have hxl : inner ℝ x (m l) < c l := (side_iff P A l x).1 (hx.2 l hlS)
    have h1 : y < U k t := (hUp k hk x).1 hxk
    have h2 : U l t < y := (hLo l hl x).1 hxl
    have h3 : c k - inner ℝ x (m k) = β k * (U k t - y) := by
      rw [hcoord]; simp only [U]; field_simp; ring
    have h4 : c k - inner ℝ x (m k) ≤ U k t - y := by rw [h3]; nlinarith
    have ht : -R0 ≤ t := by
      have := abs_inner_le_norm_of_unit he x
      have := mem_closedBall_zero_iff.1 (hsub hx)
      rw [abs_le] at *; linarith
    have h5 : U k t - U l t ≤ -g * (2 * R0 + 3 * r) := by
      rw [hG t]
      rw [abs_le] at ht0
      nlinarith
    have hd := dist_eq_of_side P A k hxk
    rw [hw k] at hd
    rw [hd]
    have h6 : -g * (2 * R0 + 3 * r) ≤ s / (958 / 1000) * (2 * R0 + 3 * r) :=
      mul_le_mul_of_nonneg_right hgs (by positivity)
    have h7 : 2 * R0 + 3 * r ≤ 131 / 2000 * kRho := by simp only [hR0_def]; linarith
    have h8 : s / (958 / 1000) * (2 * R0 + 3 * r) ≤ s / (958 / 1000) * (131 / 2000 * kRho) :=
      mul_le_mul_of_nonneg_left h7 (by positivity)
    have h9 : s / (958 / 1000) * (131 / 2000 * kRho) = 131 / 1916 * (kRho * s) := by ring
    have h10 : 2 * kRho * s / 1e13 = 2 / 1e13 * (kRho * s) := by ring
    have h11 : 7 / 100 * kRho * s = 7 / 100 * (kRho * s) := by ring
    have hks : 0 < kRho * s := by positivity
    rw [h9] at h8
    rw [h10] at hws
    rw [h11]
    linarith
  -- the crossing point of the two center lines lies in `ρD`
  have hδk : |inner ℝ p0 (P k).n - (P k).mid| ≤ w / 2 + -g * D := by
    have hd := dist_eq_of_side P A k (hp0side k hkS)
    rw [hw k] at hd
    rw [hd]
    have h3 : c k - inner ℝ p0 (m k) = β k * (U k t0 - y0) := by
      rw [hcoord]; simp only [U]; field_simp; ring
    have := (hUpp k hk).1
    have := (hLop l hl).1
    nlinarith
  have hδl : |inner ℝ p0 (P l).n - (P l).mid| ≤ w / 2 + -g * D := by
    have hd := dist_eq_of_side P A l (hp0side l hlS)
    rw [hw l] at hd
    rw [hd]
    have h3 : c l - inner ℝ p0 (m l) = β l * (U l t0 - y0) := by
      rw [hcoord]; simp only [U]; field_simp; ring
    have := (hUpp k hk).1
    have := (hLop l hl).1
    nlinarith
  have hcr := Plank.norm_sub_crossPt_le hang hδk hδl
  have hDb : D ≤ 33 / 1000 * kRho := by simp only [hD_def, hR0_def]; linarith
  have hgD : -g * D ≤ s / (958 / 1000) * D := mul_le_mul_of_nonneg_right hgs hD.le
  have h2δ : 2 * (w / 2 + -g * D) / s ≤ 2 * kRho / 1e13 + 2 * D / (958 / 1000) := by
    rw [div_le_iff₀ hs0]
    have : s / (958 / 1000) * D * 2 = 2 * D / (958 / 1000) * s := by ring
    have : 2 * kRho * s / 1e13 = 2 * kRho / 1e13 * s := by ring
    nlinarith
  have hcrnorm : ‖(P k).crossPt (P l)‖ ≤ kRho := by
    have h1 : ‖(P k).crossPt (P l)‖ ≤ ‖p0‖ + ‖p0 - (P k).crossPt (P l)‖ := by
      calc ‖(P k).crossPt (P l)‖ = ‖p0 - (p0 - (P k).crossPt (P l))‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    have h2 : s / (958 / 1000) * D ≤ 1 / (958 / 1000) * D := by
      apply mul_le_mul_of_nonneg_right _ hD.le
      exact div_le_div_of_nonneg_right hs1 (by norm_num)
    have h3 : 2 * kRho * s / 1e13 ≤ 2 * kRho / 1e13 := by
      rw [div_le_div_iff_of_pos_right (by norm_num)]; nlinarith
    linarith
  refine ⟨k, hkS, l, hlS, ⟨?_, hkc, ?_, hang, (P k).crossPt (P l), hcrnorm,
    Plank.crossPt_mem_left _ _, Plank.crossPt_mem_right hang⟩, hdist⟩
  · rintro rfl; linarith
  · unfold IsDeep; unfold IsCentral at hlc; linarith

end Annulus

end
