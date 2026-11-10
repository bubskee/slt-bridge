/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Three.Prefix

/-!
# Assembly: the weighted sublevel theorem at position three

The note's proof of Theorem "Position three" (Section 6 of `complex_middle_positions.tex`). Write
`w = ((g₁, l₁), (g₂, l₂))` with prefix pairs `g_k` and suffix forms `l_k = (a_k, b_k)`, and
`Q_k = a_k² b_k`.

1. `rpow_norm_le_weight`: `‖w‖^{1/4} ≤ W₂(g₁) W₂(g₂) W₁(l₁) W₁(l₂)`.
2. `sublevel_indicator_le`: on `‖R₃ w‖ < 1` all eleven constraints hold, so the weighted
   indicator is at most `W₂ W₂ · prefixKernel_{Q₁}(Ψ g₁, Ψ g₂) · (𝟙_suf W₁)(l₁) (𝟙_suf W₁)(l₂) ·
   𝟙{|Q₁ - Q₂| < 1}`. The only prefix–suffix coupling is the translation `c = Q₁` in
   `|p¹₀ - p²₀ + Q₁| < 1`.
3. `measurePreserving_shuffle` and Tonelli: integrate the prefix pairs first; `prefix_bound`
   bounds that integral by `B`, uniformly in `Q₁`.
4. `suffix_bound`: the remaining suffix integral is `∬_{|Q₁ - Q₂| < 1} N₃(Q₁) N₃(Q₂)`, finite by
   the translated kernel bound on `ℂ` with `N₃ = N₃ 𝟙{|Q| ≤ 1} + N₃ 𝟙{|Q| > 1} ∈ L¹ + L²`.

**Departure from the note.** The note concludes with its Lemma "Local averaging of a planar
bound" (`κ = 1`, `ν = 7/6`, `γ = 0`). Here step 4 reuses the translated `L¹ + L²` kernel bound of
the prefix instead: `N₃ ∈ L¹` near `0` (`κ = 1 < 2`) and `N₃ ∈ L²` near `∞` (`2ν = 7/3 > 2`) are
exactly the hypotheses of that lemma, and the prefix's uniform bound replaces `P₃ ≤ C`.
-/

@[expose] public section

namespace SLT.MiddlePositions.Three

open MeasureTheory Set Real Metric SLT.PositionFour SLT.PositionFour.Downstream
open scoped ENNReal NNReal

/-! ### The product weight dominates `‖w‖^{1/4}` -/

/-- From `x^{1/4} ≤ W` to `x ≤ W⁴`. -/
theorem le_pow_four_of_rpow_le {x W : ℝ} (hx : 0 ≤ x) (h : x ^ (1 / 4 : ℝ) ≤ W) : x ≤ W ^ 4 := by
  calc x = (x ^ (1 / 4 : ℝ)) ^ 4 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
    _ ≤ W ^ 4 := pow_le_pow_left₀ (Real.rpow_nonneg hx _) h 4

/-- `‖g‖ ≤ W₂(g)⁴` (sup norm). -/
theorem norm_le_W2_pow (g : Form × Form) : ‖g‖ ≤ W2 g ^ 4 := by
  have h1 := Real.rpow_nonneg (norm_nonneg g.1.1) (1 / 4 : ℝ)
  have h2 := Real.rpow_nonneg (norm_nonneg g.1.2) (1 / 4 : ℝ)
  have h3 := Real.rpow_nonneg (norm_nonneg g.2.1) (1 / 4 : ℝ)
  have h4 := Real.rpow_nonneg (norm_nonneg g.2.2) (1 / 4 : ℝ)
  rw [Prod.norm_def, Prod.norm_def, Prod.norm_def]
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;>
    exact le_pow_four_of_rpow_le (norm_nonneg _) (by unfold W2; linarith)

/-- `‖l‖ ≤ W₁(l)⁴` (sup norm). -/
theorem norm_le_W1_pow (l : Form) : ‖l‖ ≤ W1 l ^ 4 := by
  have h1 := Real.rpow_nonneg (norm_nonneg l.1) (1 / 4 : ℝ)
  have h2 := Real.rpow_nonneg (norm_nonneg l.2) (1 / 4 : ℝ)
  rw [Prod.norm_def]
  refine max_le ?_ ?_ <;>
    exact le_pow_four_of_rpow_le (norm_nonneg _) (by unfold W1; linarith)

/-- The product weight on the raw source. -/
noncomputable def productWeight (w : Row3 × Row3) : ℝ :=
  W2 w.1.1 * W2 w.2.1 * W1 w.1.2 * W1 w.2.2

/-- **The product weight dominates the moment weight**: `‖w‖^{1/4} ≤ W₂ W₂ W₁ W₁`, since every
factor is at least one and the factor of a largest entry bounds that entry's `1/4` power. -/
theorem rpow_norm_le_weight (w : Row3 × Row3) : ‖w‖ ^ (1 / 4 : ℝ) ≤ productWeight w := by
  have a1 := one_le_W2 w.1.1
  have a2 := one_le_W2 w.2.1
  have b1 := one_le_W1 w.1.2
  have b2 := one_le_W1 w.2.2
  set Pw := productWeight w with hPw
  have hPw1 : 1 ≤ Pw := by
    rw [hPw, productWeight]
    nlinarith [mul_le_mul a1 a2 zero_le_one (by linarith), mul_le_mul b1 b2 zero_le_one
      (by linarith)]
  have hge : W2 w.1.1 ≤ Pw ∧ W2 w.2.1 ≤ Pw ∧ W1 w.1.2 ≤ Pw ∧ W1 w.2.2 ≤ Pw := by
    rw [hPw, productWeight]
    refine ⟨?_, ?_, ?_, ?_⟩
    · nlinarith [mul_le_mul a2 b1 zero_le_one (by linarith),
        mul_le_mul (le_refl (W2 w.2.1 * W1 w.1.2)) b2 zero_le_one (by positivity)]
    · nlinarith [mul_le_mul a1 b1 zero_le_one (by linarith),
        mul_le_mul (le_refl (W2 w.1.1 * W1 w.1.2)) b2 zero_le_one (by positivity)]
    · nlinarith [mul_le_mul a1 a2 zero_le_one (by linarith),
        mul_le_mul (le_refl (W2 w.1.1 * W2 w.2.1)) b2 zero_le_one (by positivity)]
    · nlinarith [mul_le_mul a1 a2 zero_le_one (by linarith),
        mul_le_mul (le_refl (W2 w.1.1 * W2 w.2.1)) b1 zero_le_one (by positivity)]
  obtain ⟨c1, c2, c3, c4⟩ := hge
  have p : ∀ {W : ℝ}, 1 ≤ W → W ≤ Pw → W ^ 4 ≤ Pw ^ 4 := fun h1 h2 =>
    pow_le_pow_left₀ (by linarith) h2 4
  have hw : ‖w‖ ≤ Pw ^ 4 := by
    rw [Prod.norm_def, Prod.norm_def, Prod.norm_def]
    exact max_le (max_le ((norm_le_W2_pow _).trans (p a1 c1)) ((norm_le_W1_pow _).trans (p b1 c3)))
      (max_le ((norm_le_W2_pow _).trans (p a2 c2)) ((norm_le_W1_pow _).trans (p b2 c4)))
  calc ‖w‖ ^ (1 / 4 : ℝ) ≤ (Pw ^ 4) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) hw (by norm_num)
    _ = Pw := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num

/-! ### The sublevel set and the integrand bound -/

/-- The suffix coupling variable `Q = q₁ = a² b` of a suffix form `l = (a, b)`. -/
def suffixQ (l : Form) : ℂ := l.1 ^ 2 * l.2

/-- The integrand dominating the weighted sublevel indicator. -/
noncomputable def sublevelBound (w : Row3 × Row3) : ℝ≥0∞ :=
  ENNReal.ofReal (W2 w.1.1) * ENNReal.ofReal (W2 w.2.1) *
    prefixKernel (suffixQ w.1.2) (twoCube w.1.1) (twoCube w.2.1) *
    (suffixWeight w.1.2 * suffixWeight w.2.2 *
      (ball (0 : ℂ) 1).indicator 1 (suffixQ w.1.2 - suffixQ w.2.2))

/-- **The eleven constraints.** On `‖R₃ w‖ < 1`, the weighted indicator is dominated. -/
theorem sublevel_indicator_le (w : Row3 × Row3) :
    {w : Row3 × Row3 | ‖R3 w‖ < 1}.indicator (fun w => ENNReal.ofReal (‖w‖ ^ (1 / 4 : ℝ))) w ≤
      sublevelBound w := by
  by_cases hw : ‖R3 w‖ < 1
  · rw [indicator_of_mem (show w ∈ {w : Row3 × Row3 | ‖R3 w‖ < 1} from hw)]
    have hi := (pi_norm_lt_iff one_pos).mp hw
    have h0 : ‖twoCube w.1.1 2‖ < 1 := by simpa [R3, generators] using hi 0
    have h1 : ‖twoCube w.1.1 3‖ < 1 := by simpa [R3, generators] using hi 1
    have h2 : ‖w.1.2.1 * w.1.2.2 ^ 2‖ < 1 := by simpa [R3, generators, cube] using hi 2
    have h3 : ‖w.1.2.2 ^ 3‖ < 1 := by simpa [R3, generators, cube] using hi 3
    have h4 : ‖twoCube w.2.1 2‖ < 1 := by simpa [R3, generators] using hi 4
    have h5 : ‖twoCube w.2.1 3‖ < 1 := by simpa [R3, generators] using hi 5
    have h6 : ‖w.2.2.1 * w.2.2.2 ^ 2‖ < 1 := by simpa [R3, generators, cube] using hi 6
    have h7 : ‖w.2.2.2 ^ 3‖ < 1 := by simpa [R3, generators, cube] using hi 7
    have h8 : ‖twoCube w.1.1 1 - twoCube w.2.1 1‖ < 1 := by simpa [R3, generators] using hi 8
    have h9 : ‖w.1.2.1 ^ 2 * w.1.2.2 - w.2.2.1 ^ 2 * w.2.2.2‖ < 1 := by
      simpa [R3, generators, cube] using hi 9
    have h10 : ‖twoCube w.1.1 0 - twoCube w.2.1 0 + w.1.2.1 ^ 2 * w.1.2.2‖ < 1 := by
      simpa [R3, generators, cube] using hi 10
    have hb1 : boxInd (twoCube w.1.1) = 1 := by
      rw [boxInd, indicator_of_mem]; · rfl
      rw [mem_ball_zero_iff, Prod.norm_def]; exact max_lt h0 h1
    have hb2 : boxInd (twoCube w.2.1) = 1 := by
      rw [boxInd, indicator_of_mem]; · rfl
      rw [mem_ball_zero_iff, Prod.norm_def]; exact max_lt h4 h5
    have hc : (ball ((-suffixQ w.1.2, 0) : ℂ × ℂ) 1).indicator (1 : ℂ × ℂ → ℝ≥0∞)
        (lamOf (twoCube w.1.1) - lamOf (twoCube w.2.1)) = 1 := by
      rw [indicator_of_mem]; · rfl
      rw [mem_ball, dist_eq_norm, Prod.norm_def]
      simp only [lamOf, suffixQ, Prod.fst_sub, Prod.snd_sub, sub_neg_eq_add, sub_zero]
      exact max_lt h10 h8
    have hs1 : w.1.2 ∈ suffixSet := ⟨h2, h3⟩
    have hs2 : w.2.2 ∈ suffixSet := ⟨h6, h7⟩
    have hq : (ball (0 : ℂ) 1).indicator (1 : ℂ → ℝ≥0∞) (suffixQ w.1.2 - suffixQ w.2.2) = 1 := by
      rw [indicator_of_mem]; · rfl
      rw [mem_ball_zero_iff]; exact h9
    rw [sublevelBound, prefixKernel, hb1, hb2, hc, hq, suffixWeight, suffixWeight,
      indicator_of_mem hs1, indicator_of_mem hs2]
    simp only [mul_one]
    have e1 := (one_le_W2 w.1.1); have e2 := (one_le_W2 w.2.1)
    have e3 := (one_le_W1 w.1.2); have e4 := (one_le_W1 w.2.2)
    rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ((rpow_norm_le_weight w).trans (le_of_eq ?_))
    rw [productWeight]; ring
  · rw [indicator_of_notMem (show w ∉ {w : Row3 × Row3 | ‖R3 w‖ < 1} from hw)]; exact bot_le

/-! ### Measurability -/

/-- A unit-ball indicator with measurably moving centre and point is measurable. -/
theorem measurable_indicator_ball_comp {α E : Type*} [MeasurableSpace α] [PseudoMetricSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E] {z x : α → E}
    (hz : Measurable z) (hx : Measurable x) :
    Measurable fun a => (ball (z a) 1).indicator (1 : E → ℝ≥0∞) (x a) := by
  have e : (fun a => (ball (z a) 1).indicator (1 : E → ℝ≥0∞) (x a)) =
      {a | dist (x a) (z a) < 1}.indicator 1 := by
    funext a
    by_cases ha : dist (x a) (z a) < 1
    · rw [indicator_of_mem (show x a ∈ ball (z a) 1 from ha),
        indicator_of_mem (show a ∈ {a | dist (x a) (z a) < 1} from ha)]; rfl
    · rw [indicator_of_notMem (show x a ∉ ball (z a) 1 from ha),
        indicator_of_notMem (show a ∉ {a | dist (x a) (z a) < 1} from ha)]
  rw [e]
  exact measurable_one.indicator (measurableSet_lt (hx.dist hz) measurable_const)

/-- `suffixQ` is measurable. -/
theorem measurable_suffixQ : Measurable suffixQ := by unfold suffixQ; fun_prop

/-- The prefix kernel with measurably moving translation and cubics is measurable. -/
theorem measurable_prefixKernel_comp {α : Type*} [MeasurableSpace α] {c : α → ℂ}
    {P₁ P₂ : α → Cubic} (hc : Measurable c) (h₁ : Measurable P₁) (h₂ : Measurable P₂) :
    Measurable fun a => prefixKernel (c a) (P₁ a) (P₂ a) := by
  have hb1 : Measurable fun a => boxInd (P₁ a) := measurable_boxInd.comp h₁
  have hb2 : Measurable fun a => boxInd (P₂ a) := measurable_boxInd.comp h₂
  have hi : Measurable fun a => (ball ((-c a, 0) : ℂ × ℂ) 1).indicator (1 : ℂ × ℂ → ℝ≥0∞)
      (lamOf (P₁ a) - lamOf (P₂ a)) :=
    measurable_indicator_ball_comp (hc.neg.prodMk measurable_const)
      ((measurable_lamOf.comp h₁).sub (measurable_lamOf.comp h₂))
  unfold prefixKernel
  exact (hb1.mul hb2).mul hi
/-! ### Rearranging the twelve coordinates -/

/-- The shuffle `((g₁, l₁), (g₂, l₂)) ↦ ((g₁, g₂), (l₁, l₂))` preserves Lebesgue measure. -/
theorem measurePreserving_shuffle {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [SFinite (volume : Measure α)] [SFinite (volume : Measure β)] :
    MeasurePreserving (fun w : (α × β) × (α × β) => ((w.1.1, w.2.1), (w.1.2, w.2.2)))
      volume volume := by
  have h1 := measurePreserving_prodAssoc (volume : Measure α) (volume : Measure β)
    (volume : Measure (α × β))
  have h2 := (MeasurePreserving.id (volume : Measure α)).prod
    (MeasurePreserving.symm _ (measurePreserving_prodAssoc (volume : Measure β)
      (volume : Measure α) (volume : Measure β)))
  have h3 := (MeasurePreserving.id (volume : Measure α)).prod
    ((Measure.measurePreserving_swap (μ := (volume : Measure β)) (ν := (volume : Measure α))).prod
      (MeasurePreserving.id (volume : Measure β)))
  have h4 := (MeasurePreserving.id (volume : Measure α)).prod
    (measurePreserving_prodAssoc (volume : Measure α) (volume : Measure β) (volume : Measure β))
  have h5 := MeasurePreserving.symm _ (measurePreserving_prodAssoc (volume : Measure α)
    (volume : Measure α) (volume : Measure (β × β)))
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

/-! ### The suffix double integral -/

/-- **The suffix bound**: `∫∫ (𝟙_suf W₁)(l₁) (𝟙_suf W₁)(l₂) 𝟙{|Q₁ - Q₂| < 1} < ∞`. -/
theorem suffix_bound :
    ∫⁻ l₁ : Form, ∫⁻ l₂ : Form, suffixWeight l₁ * suffixWeight l₂ *
      (ball (0 : ℂ) 1).indicator 1 (suffixQ l₁ - suffixQ l₂) < ∞ := by
  have hk : ∀ x : ℂ, Measurable fun y : ℂ => (ball (0 : ℂ) 1).indicator (1 : ℂ → ℝ≥0∞) (x - y) :=
    fun x => (measurable_one.indicator measurableSet_ball).comp (measurable_const.sub measurable_id)
  set H : ℂ → ℝ≥0∞ := fun x => ∫⁻ y, kernelN3 y * (ball (0 : ℂ) 1).indicator 1 (x - y) with hH
  have hHm : Measurable H :=
    ((measurable_kernelN3.comp measurable_snd).mul ((measurable_one.indicator
      measurableSet_ball).comp (measurable_fst.sub measurable_snd))).lintegral_prod_right'
  have inner : ∀ l₁ : Form, ∫⁻ l₂ : Form, suffixWeight l₁ * suffixWeight l₂ *
      (ball (0 : ℂ) 1).indicator 1 (suffixQ l₁ - suffixQ l₂) =
        suffixWeight l₁ * H (suffixQ l₁) := by
    intro l₁
    have hm : Measurable fun l₂ : Form => suffixWeight l₂ *
        (ball (0 : ℂ) 1).indicator (1 : ℂ → ℝ≥0∞) (suffixQ l₁ - suffixQ l₂) :=
      measurable_suffixWeight.mul ((hk _).comp measurable_suffixQ)
    simp_rw [mul_assoc]
    rw [lintegral_const_mul _ hm]
    congr 1
    exact lintegral_suffixWeight_mul (hk (suffixQ l₁))
  have hf1 : Measurable ((closedBall (0 : ℂ) 1).indicator kernelN3) :=
    measurable_kernelN3.indicator measurableSet_closedBall
  have hf2 : Measurable ((closedBall (0 : ℂ) 1)ᶜ.indicator kernelN3) :=
    measurable_kernelN3.indicator measurableSet_closedBall.compl
  have hI1 : ∫⁻ x, (closedBall (0 : ℂ) 1).indicator kernelN3 x < ∞ := by
    rw [lintegral_indicator measurableSet_closedBall]; exact lintegral_kernelN3_near_lt_top
  have hI2 : ∫⁻ x, (closedBall (0 : ℂ) 1)ᶜ.indicator kernelN3 x ^ 2 < ∞ := by
    rw [lintegral_indicator_sq measurableSet_closedBall.compl]
    have : (closedBall (0 : ℂ) 1)ᶜ = {Q : ℂ | 1 < ‖Q‖} := by
      ext Q; simp
    rw [this]; exact lintegral_kernelN3_far_sq_lt_top
  calc ∫⁻ l₁ : Form, ∫⁻ l₂ : Form, suffixWeight l₁ * suffixWeight l₂ *
        (ball (0 : ℂ) 1).indicator 1 (suffixQ l₁ - suffixQ l₂)
      = ∫⁻ l₁ : Form, suffixWeight l₁ * H (suffixQ l₁) := lintegral_congr inner
    _ = ∫⁻ x, kernelN3 x * H x := lintegral_suffixWeight_mul hHm
    _ = ∫⁻ x, ∫⁻ y, (ball (0 : ℂ) 1).indicator 1 (x - y) * (kernelN3 x * kernelN3 y) := by
        refine lintegral_congr fun x => ?_
        have hm : Measurable fun y =>
            kernelN3 y * (ball (0 : ℂ) 1).indicator (1 : ℂ → ℝ≥0∞) (x - y) :=
          measurable_kernelN3.mul (hk x)
        rw [hH]; simp only
        rw [← lintegral_const_mul _ hm]
        refine lintegral_congr fun y => ?_
        ring
    _ ≤ _ := lintegral_kernel_le volume hf1 hf2 (fun x => by
          rw [indicator_self_add_compl_apply]) 0
    _ < ∞ := kernel_bound_lt_top volume hI1 hI2

/-! ### The theorem -/

/-- The integrand on the shuffled coordinates `((g₁, g₂), (l₁, l₂))`. -/
noncomputable def shuffledBound (v : ((Form × Form) × (Form × Form)) × (Form × Form)) : ℝ≥0∞ :=
  ENNReal.ofReal (W2 v.1.1) * ENNReal.ofReal (W2 v.1.2) *
    prefixKernel (suffixQ v.2.1) (twoCube v.1.1) (twoCube v.1.2) *
    (suffixWeight v.2.1 * suffixWeight v.2.2 *
      (ball (0 : ℂ) 1).indicator 1 (suffixQ v.2.1 - suffixQ v.2.2))

/-- The prefix factor of `shuffledBound` is measurable. -/
theorem measurable_prefixFactor :
    Measurable fun v : ((Form × Form) × (Form × Form)) × (Form × Form) =>
      ENNReal.ofReal (W2 v.1.1) * ENNReal.ofReal (W2 v.1.2) *
        prefixKernel (suffixQ v.2.1) (twoCube v.1.1) (twoCube v.1.2) := by
  have h0 : Measurable fun v : ((Form × Form) × (Form × Form)) × (Form × Form) =>
      ENNReal.ofReal (W2 v.1.1) * ENNReal.ofReal (W2 v.1.2) :=
    (measurable_W2.ennreal_ofReal.comp measurable_fst.fst).mul
      (measurable_W2.ennreal_ofReal.comp measurable_fst.snd)
  have h1 : Measurable fun v : ((Form × Form) × (Form × Form)) × (Form × Form) =>
      prefixKernel (suffixQ v.2.1) (twoCube v.1.1) (twoCube v.1.2) :=
    measurable_prefixKernel_comp (measurable_suffixQ.comp measurable_snd.fst)
      (measurable_twoCube.comp measurable_fst.fst) (measurable_twoCube.comp measurable_fst.snd)
  exact h0.mul h1

/-- The suffix factor of `shuffledBound` is measurable. -/
theorem measurable_suffixFactor : Measurable fun ll : Form × Form =>
    suffixWeight ll.1 * suffixWeight ll.2 *
      (ball (0 : ℂ) 1).indicator (1 : ℂ → ℝ≥0∞) (suffixQ ll.1 - suffixQ ll.2) :=
  ((measurable_suffixWeight.comp measurable_fst).mul
    (measurable_suffixWeight.comp measurable_snd)).mul
    ((measurable_one.indicator measurableSet_ball).comp
      ((measurable_suffixQ.comp measurable_fst).sub (measurable_suffixQ.comp measurable_snd)))

/-- `shuffledBound` is measurable. -/
theorem measurable_shuffledBound : Measurable shuffledBound := by
  have h : Measurable fun v : ((Form × Form) × (Form × Form)) × (Form × Form) =>
      suffixWeight v.2.1 * suffixWeight v.2.2 *
        (ball (0 : ℂ) 1).indicator (1 : ℂ → ℝ≥0∞) (suffixQ v.2.1 - suffixQ v.2.2) :=
    measurable_suffixFactor.comp measurable_snd
  exact measurable_prefixFactor.mul h

/-- `R₃` is continuous. -/
theorem continuous_R3 : Continuous R3 := by
  unfold R3 generators twoCube cube; fun_prop

/-- The unit sublevel set of `R₃` is measurable. -/
theorem measurableSet_sublevelThree : MeasurableSet {w : Row3 × Row3 | ‖R3 w‖ < 1} :=
  measurableSet_lt continuous_R3.norm.measurable measurable_const

/-- The volume on pairs of prefix pairs is σ-finite (instance search alone gives up on this
four-fold product). -/
theorem sigmaFinite_volume_prefixPairs :
    SigmaFinite (volume : Measure ((Form × Form) × (Form × Form))) := by
  have : SigmaFinite (volume : Measure (Form × Form)) := inferInstance
  exact Measure.prod.instSigmaFinite

/-- **Theorem (position three)**, from the interface: `∫_{‖R₃ w‖ < 1} ‖w‖^{1/4} dw < ∞`. -/
theorem sublevelThree_of_interface {C : ℝ} (hW : WeightedTwoCubeBound C) (hF : LocallyIntegrableF)
    (hQ : ∀ t : ℝ, 1 < t → t < 2 → ∃ K, FullPlaneQuadratic t K) : SublevelThree := by
  obtain ⟨K₁, hK₁⟩ := hQ (4 / 3) (by norm_num) (by norm_num)
  obtain ⟨K₂, hK₂⟩ := hQ (11 / 8) (by norm_num) (by norm_num)
  obtain ⟨B, hB, hPB⟩ := prefix_bound hW hF hK₁ hK₂
  have hA := measurable_prefixFactor
  have hS := measurable_suffixFactor
  have hAl : ∀ ll : Form × Form, Measurable fun gg : (Form × Form) × (Form × Form) =>
      ENNReal.ofReal (W2 gg.1) * ENNReal.ofReal (W2 gg.2) *
        prefixKernel (suffixQ ll.1) (twoCube gg.1) (twoCube gg.2) :=
    fun ll => ((measurable_W2.ennreal_ofReal.comp measurable_fst).mul
      (measurable_W2.ennreal_ofReal.comp measurable_snd)).mul
      (measurable_prefixKernel_comp measurable_const (measurable_twoCube.comp measurable_fst)
        (measurable_twoCube.comp measurable_snd))
  have := sigmaFinite_volume_prefixPairs
  unfold SublevelThree
  rw [← lintegral_indicator measurableSet_sublevelThree]
  calc ∫⁻ w, {w : Row3 × Row3 | ‖R3 w‖ < 1}.indicator
        (fun w => ENNReal.ofReal (‖w‖ ^ (1 / 4 : ℝ))) w
      ≤ ∫⁻ w, sublevelBound w := lintegral_mono sublevel_indicator_le
    _ = ∫⁻ w : Row3 × Row3, shuffledBound ((w.1.1, w.2.1), (w.1.2, w.2.2)) := rfl
    _ = ∫⁻ v, shuffledBound v :=
        (measurePreserving_shuffle (α := Form × Form) (β := Form)).lintegral_comp
          measurable_shuffledBound
    _ = ∫⁻ ll : Form × Form, ∫⁻ gg : (Form × Form) × (Form × Form), shuffledBound (gg, ll) := by
        rw [Measure.volume_eq_prod ((Form × Form) × (Form × Form)) (Form × Form),
          lintegral_prod_symm _ measurable_shuffledBound.aemeasurable]
    _ ≤ ∫⁻ ll : Form × Form, B * (suffixWeight ll.1 * suffixWeight ll.2 *
          (ball (0 : ℂ) 1).indicator 1 (suffixQ ll.1 - suffixQ ll.2)) := by
        refine lintegral_mono fun ll => ?_
        simp only [shuffledBound]
        rw [lintegral_mul_const _ (hAl ll)]
        gcongr
        rw [Measure.volume_eq_prod (Form × Form) (Form × Form),
          lintegral_prod _ (hAl ll).aemeasurable]
        exact hPB _
    _ = B * ∫⁻ ll : Form × Form, suffixWeight ll.1 * suffixWeight ll.2 *
          (ball (0 : ℂ) 1).indicator 1 (suffixQ ll.1 - suffixQ ll.2) := lintegral_const_mul _ hS
    _ < ∞ := by
        rw [Measure.volume_eq_prod Form Form, lintegral_prod _ hS.aemeasurable]
        exact ENNReal.mul_lt_top hB suffix_bound

end SLT.MiddlePositions.Three
