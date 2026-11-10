/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Two.Planar

/-!
# The one-form prefix at position two

Section 4 of `complex_middle_positions.tex` (Lemma "One-form prefix decay"), replaced by a
stronger and simpler statement. The two prefix forms are `l_k = (a_k, b_k)`, with prefix cubics
`p^k = l_k³ = (a_k³, a_k² b_k, a_k b_k², b_k³)`. The prefix constraints are
`|b_k³| < 1`, `|a_k b_k²| < 1` and `|a₁² b₁ - a₂² b₂| < 1` (`preSet`), and the weight is
`V = 1 + ‖l₁‖^{1/4} + ‖l₂‖^{1/4}`.

**`lintegral_pre_lt_top`: `∫∫_{preSet} V dl₁ dl₂ < ∞`, with no coupling to the suffix.** The note
proves the decay `P₂(c) ≤ C (1 + |c|)^{-9/4}` of the prefix mass at the coupling level
`|a₁³ - a₂³ - c| < 1`, by a three-to-one cube substitution on a slab, and needs it because its
suffix kernel decays only like `|Q|^{-1/4}`. But `P₂` is integrable in `c`: its integral is `π`
times the integral here. With the suffix kernel bounded uniformly on unit `Q`-discs
(`setLIntegral_box_F_le`), finiteness of the prefix integral is all the assembly uses, so the
cube substitution is not needed.

The proof is the note's transverse-area bound without the slab. Where `|a₁| ≤ |a₂|`, the coupling
puts `b₂` in a disc of radius `|a₂|^{-2}` (`volume_coupling_le`), and `|a₁ b₁²| < 1` puts `b₁` in
a disc of area `π min(1, |a₁|^{-1})` (`volume_prefix_le`). With `φ(x) = max(1, x)` this leaves
`3π² φ(|a₂|)^{1/4 - 4} φ(|a₁|)^{-1} ≤ 3π² φ(|a₁|)^{-19/8} φ(|a₂|)^{-19/8}`, and
`∫_ℂ φ(|a|)^{-19/8} < ∞`. The other half `|a₂| ≤ |a₁|` follows by symmetry.
-/

@[expose] public section

namespace SLT.MiddlePositions.Two

open MeasureTheory Set Real Metric SLT.PositionFour
open scoped ENNReal NNReal

/-! ### The prefix integrand -/

/-- The prefix constraints at position two, in the raw variables `l_k = (a_k, b_k)`:
`|b_k³| < 1`, `|a_k b_k²| < 1` (`k = 1, 2`) and `|a₁² b₁ - a₂² b₂| < 1`. -/
def preSet : Set (Form × Form) :=
  {l | ‖l.1.2 ^ 3‖ < 1 ∧ ‖l.1.1 * l.1.2 ^ 2‖ < 1 ∧ ‖l.2.2 ^ 3‖ < 1 ∧ ‖l.2.1 * l.2.2 ^ 2‖ < 1 ∧
    ‖l.1.1 ^ 2 * l.1.2 - l.2.1 ^ 2 * l.2.2‖ < 1}

/-- The prefix weight `V(l₁, l₂) = 1 + ‖l₁‖^{1/4} + ‖l₂‖^{1/4}`. -/
noncomputable def V (l₁ l₂ : Form) : ℝ := 1 + ‖l₁‖ ^ (1 / 4 : ℝ) + ‖l₂‖ ^ (1 / 4 : ℝ)

/-- The prefix integrand `V 𝟙_{preSet}`. -/
noncomputable def pre (l₁ l₂ : Form) : ℝ≥0∞ :=
  preSet.indicator (fun l => ENNReal.ofReal (V l.1 l.2)) (l₁, l₂)

/-- `preSet` is measurable. -/
theorem measurableSet_preSet : MeasurableSet preSet := by
  have h : ∀ f : Form × Form → ℂ, Continuous f → MeasurableSet {l | ‖f l‖ < 1} := fun f hf =>
    measurableSet_lt hf.norm.measurable measurable_const
  exact (h _ (by fun_prop)).inter ((h _ (by fun_prop)).inter ((h _ (by fun_prop)).inter
    ((h _ (by fun_prop)).inter (h _ (by fun_prop)))))

/-- The prefix integrand is measurable. -/
theorem measurable_pre : Measurable fun l : Form × Form => pre l.1 l.2 := by
  have hV : Measurable fun l : Form × Form => ENNReal.ofReal (V l.1 l.2) := by
    unfold V; fun_prop
  exact hV.indicator measurableSet_preSet

/-- The prefix integrand is symmetric in the two rows. -/
theorem pre_comm (l₁ l₂ : Form) : pre l₁ l₂ = pre l₂ l₁ := by
  have hS : (l₁, l₂) ∈ preSet ↔ (l₂, l₁) ∈ preSet := by
    simp only [preSet, mem_ofPred_eq]
    rw [norm_sub_rev]
    tauto
  have hV : V l₁ l₂ = V l₂ l₁ := by unfold V; ring
  unfold pre
  by_cases h : (l₁, l₂) ∈ preSet
  · rw [indicator_of_mem h, indicator_of_mem (hS.mp h), hV]
  · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hS.mpr h'))]

/-! ### Two transverse areas -/

/-- The coupling disc: `{b : |b| < 1, |w - a² b| < 1}` has area at most `π max(1, |a|)^{-4}`. -/
theorem volume_coupling_le (w a : ℂ) :
    volume {b : ℂ | ‖b‖ < 1 ∧ ‖w - a ^ 2 * b‖ < 1} ≤ ENNReal.ofReal (π * max 1 ‖a‖ ^ (-4 : ℝ)) := by
  rcases le_or_gt ‖a‖ 1 with ha | ha
  · rw [max_eq_left ha, Real.one_rpow, mul_one]
    calc volume {b : ℂ | ‖b‖ < 1 ∧ ‖w - a ^ 2 * b‖ < 1} ≤ volume (ball (0 : ℂ) 1) :=
          measure_mono fun b hb => mem_ball_zero_iff.mpr hb.1
      _ = _ := by
          rw [Complex.volume_ball, ENNReal.ofReal_one, one_pow, one_mul,
            ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
  · have ha0 : a ≠ 0 := norm_pos_iff.mp (by linarith)
    have ha' : 0 < ‖a‖ := by linarith
    rw [max_eq_right ha.le]
    calc volume {b : ℂ | ‖b‖ < 1 ∧ ‖w - a ^ 2 * b‖ < 1}
        ≤ volume (ball (w / a ^ 2) (‖a‖ ^ 2)⁻¹) := by
          refine measure_mono fun b hb => ?_
          rw [mem_ball, dist_eq_norm]
          have e : b - w / a ^ 2 = -(w - a ^ 2 * b) / a ^ 2 := by field_simp; ring
          rw [e, norm_div, norm_neg, norm_pow, div_lt_iff₀ (by positivity), inv_mul_cancel₀
            (by positivity)]
          exact hb.2
      _ = _ := by
          rw [Complex.volume_ball, ← ENNReal.ofReal_pow (by positivity),
            ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity),
            mul_comm]
          congr 2
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.inv_rpow (by positivity),
            ← Real.rpow_mul (by positivity), ← Real.rpow_neg_one, ← Real.rpow_mul ha'.le]
          norm_num

/-- The prefix disc: `{b : |b³| < 1, |a b²| < 1}` has area at most `π max(1, |a|)^{-1}`. -/
theorem volume_prefix_le (a : ℂ) :
    volume {b : ℂ | ‖b ^ 3‖ < 1 ∧ ‖a * b ^ 2‖ < 1} ≤ ENNReal.ofReal (π * max 1 ‖a‖ ^ (-1 : ℝ)) := by
  rcases le_or_gt ‖a‖ 1 with ha | ha
  · rw [max_eq_left ha, Real.one_rpow, mul_one]
    calc volume {b : ℂ | ‖b ^ 3‖ < 1 ∧ ‖a * b ^ 2‖ < 1} ≤ volume (ball (0 : ℂ) 1) := by
          refine measure_mono fun b hb => mem_ball_zero_iff.mpr ?_
          have := hb.1
          rw [norm_pow] at this
          exact (pow_lt_one_iff_of_nonneg (norm_nonneg b) (by norm_num)).mp this
      _ = _ := by
          rw [Complex.volume_ball, ENNReal.ofReal_one, one_pow, one_mul,
            ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
  · have ha' : 0 < ‖a‖ := by linarith
    rw [max_eq_right ha.le]
    have hr : (‖a‖ ^ (-(1 / 2) : ℝ)) ^ 2 = ‖a‖ ^ (-1 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha'.le]; norm_num
    calc volume {b : ℂ | ‖b ^ 3‖ < 1 ∧ ‖a * b ^ 2‖ < 1}
        ≤ volume (ball (0 : ℂ) (‖a‖ ^ (-(1 / 2) : ℝ))) := by
          refine measure_mono fun b hb => mem_ball_zero_iff.mpr ?_
          have h2 := hb.2
          rw [norm_mul, norm_pow] at h2
          refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
          rw [hr, Real.rpow_neg_one, ← one_div, lt_div_iff₀' ha']
          exact h2
      _ = _ := by
          rw [Complex.volume_ball, ← ENNReal.ofReal_pow (by positivity), hr,
            ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity),
            mul_comm]

/-! ### The half `|a₁| ≤ |a₂|` -/

/-- `|b| < 1` from `|b³| < 1`. -/
theorem norm_lt_one_of_cube {b : ℂ} (h : ‖b ^ 3‖ < 1) : ‖b‖ < 1 := by
  rw [norm_pow] at h
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg b) (by norm_num)).mp h

/-- The constant `∫_ℂ max(1, |a|)^{-19/8}`. -/
noncomputable def Cphi : ℝ≥0∞ := ∫⁻ a : ℂ, ENNReal.ofReal (max 1 ‖a‖ ^ (-(19 / 8) : ℝ))

/-- `∫_ℂ max(1, |a|)^{-19/8} < ∞`. -/
theorem Cphi_lt_top : Cphi < ∞ := lintegral_max_one_rpow_neg_lt_top (by norm_num)

/-- The half of the prefix integrand where `|a₁| ≤ |a₂|`. -/
noncomputable def pre1 (l₁ l₂ : Form) : ℝ≥0∞ :=
  {l : Form × Form | ‖l.1.1‖ ≤ ‖l.2.1‖}.indicator (fun l => pre l.1 l.2) (l₁, l₂)

/-- The half integrand is measurable. -/
theorem measurable_pre1 : Measurable fun l : Form × Form => pre1 l.1 l.2 :=
  measurable_pre.indicator (measurableSet_le (by fun_prop) (by fun_prop))

/-- The prefix weight is at most `3 max(1, |a₂|)^{1/4}` where `|a₁| ≤ |a₂|` and `|b₁|, |b₂| < 1`. -/
theorem V_le {l₁ l₂ : Form} (h12 : ‖l₁.1‖ ≤ ‖l₂.1‖) (hb₁ : ‖l₁.2‖ < 1) (hb₂ : ‖l₂.2‖ < 1) :
    V l₁ l₂ ≤ 3 * max 1 ‖l₂.1‖ ^ (1 / 4 : ℝ) := by
  have h1 : ‖l₁‖ ≤ max 1 ‖l₂.1‖ := by
    rw [Prod.norm_def]
    exact max_le (h12.trans (le_max_right _ _)) (hb₁.le.trans (le_max_left _ _))
  have h2 : ‖l₂‖ ≤ max 1 ‖l₂.1‖ := by
    rw [Prod.norm_def]; exact max_le (le_max_right _ _) (hb₂.le.trans (le_max_left _ _))
  have e1 := Real.rpow_le_rpow (norm_nonneg _) h1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have e2 := Real.rpow_le_rpow (norm_nonneg _) h2 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have e3 : 1 ≤ max 1 ‖l₂.1‖ ^ (1 / 4 : ℝ) := Real.one_le_rpow (le_max_left _ _) (by norm_num)
  unfold V; linarith

/-- The first-row constraints `|b₁³| < 1`, `|a₁ b₁²| < 1`. -/
def rowSet : Set Form := {l | ‖l.2 ^ 3‖ < 1 ∧ ‖l.1 * l.2 ^ 2‖ < 1}

/-- **The second-row integral** where `|a₁| ≤ |a₂|`:
`∫ pre1(l₁, l₂) dl₂ ≤ 3π max(1, |a₁|)^{-11/8} 𝟙_{rowSet}(l₁) · Cphi`. -/
theorem lintegral_pre1_le (l₁ : Form) :
    ∫⁻ l₂, pre1 l₁ l₂ ≤ rowSet.indicator
      (fun l => ENNReal.ofReal (3 * π * max 1 ‖l.1‖ ^ (-(11 / 8) : ℝ))) l₁ * Cphi := by
  by_cases h1 : l₁ ∈ rowSet
  swap
  · have : ∀ l₂, pre1 l₁ l₂ = 0 := fun l₂ => by
      unfold pre1 pre
      by_cases h : (l₁, l₂) ∈ preSet
      · exact absurd ⟨h.1, h.2.1⟩ h1
      · simp [indicator, h]
    simp [this]
  rw [indicator_of_mem h1]
  obtain ⟨a₁, b₁⟩ := l₁
  have hb₁ : ‖b₁‖ < 1 := norm_lt_one_of_cube h1.1
  set c₁ := ENNReal.ofReal (3 * π * max 1 ‖a₁‖ ^ (-(11 / 8) : ℝ))
  have hinner : ∀ a₂ : ℂ, ∫⁻ b₂, pre1 (a₁, b₁) (a₂, b₂) ≤
      c₁ * ENNReal.ofReal (max 1 ‖a₂‖ ^ (-(19 / 8) : ℝ)) := by
    intro a₂
    by_cases h12 : ‖a₁‖ ≤ ‖a₂‖
    · set T := {b : ℂ | ‖b‖ < 1 ∧ ‖a₁ ^ 2 * b₁ - a₂ ^ 2 * b‖ < 1}
      have hT : MeasurableSet T :=
        (measurableSet_lt (f := fun b : ℂ => ‖b‖) (by fun_prop) measurable_const).inter
          (measurableSet_lt (f := fun b : ℂ => ‖a₁ ^ 2 * b₁ - a₂ ^ 2 * b‖) (by fun_prop)
            measurable_const)
      have hpt : ∀ b₂, pre1 (a₁, b₁) (a₂, b₂) ≤
          T.indicator (fun _ => ENNReal.ofReal (3 * max 1 ‖a₂‖ ^ (1 / 4 : ℝ))) b₂ := by
        intro b₂
        unfold pre1 pre
        by_cases h : ((a₁, b₁), (a₂, b₂)) ∈ preSet
        · have hb₂ : ‖b₂‖ < 1 := norm_lt_one_of_cube h.2.2.1
          have hT' : b₂ ∈ T := ⟨hb₂, h.2.2.2.2⟩
          rw [indicator_of_mem (show ((a₁, b₁), (a₂, b₂)) ∈
            {l : Form × Form | ‖l.1.1‖ ≤ ‖l.2.1‖} from h12), indicator_of_mem h,
            indicator_of_mem hT']
          exact ENNReal.ofReal_le_ofReal (V_le h12 hb₁ hb₂)
        · simp [indicator, h]
      set m₁ := max 1 ‖a₁‖
      set m₂ := max 1 ‖a₂‖
      have hm₁ : 0 < m₁ := lt_of_lt_of_le one_pos (le_max_left _ _)
      have hm₂ : 0 < m₂ := lt_of_lt_of_le one_pos (le_max_left _ _)
      have hm12 : m₁ ≤ m₂ := max_le_max le_rfl h12
      calc ∫⁻ b₂, pre1 (a₁, b₁) (a₂, b₂)
          ≤ ∫⁻ b₂, T.indicator (fun _ => ENNReal.ofReal (3 * m₂ ^ (1 / 4 : ℝ))) b₂ :=
            lintegral_mono hpt
        _ = ENNReal.ofReal (3 * m₂ ^ (1 / 4 : ℝ)) * volume T := lintegral_indicator_const hT _
        _ ≤ ENNReal.ofReal (3 * m₂ ^ (1 / 4 : ℝ)) * ENNReal.ofReal (π * m₂ ^ (-4 : ℝ)) := by
            gcongr; exact volume_coupling_le _ _
        _ ≤ c₁ * ENNReal.ofReal (m₂ ^ (-(19 / 8) : ℝ)) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            have e1 : m₂ ^ (1 / 4 : ℝ) * m₂ ^ (-4 : ℝ) =
                m₂ ^ (-(19 / 8) : ℝ) * m₂ ^ (-(11 / 8) : ℝ) := by
              rw [rpow_mul_rpow_eq hm₂ (by norm_num : (1 / 4 : ℝ) + -4 = -(15 / 4)),
                rpow_mul_rpow_eq hm₂ (by norm_num : -(19 / 8 : ℝ) + -(11 / 8) = -(15 / 4))]
            have e2 : m₂ ^ (-(11 / 8) : ℝ) ≤ m₁ ^ (-(11 / 8) : ℝ) :=
              Real.rpow_le_rpow_of_nonpos hm₁ hm12 (by norm_num)
            calc 3 * m₂ ^ (1 / 4 : ℝ) * (π * m₂ ^ (-4 : ℝ))
                = 3 * π * (m₂ ^ (1 / 4 : ℝ) * m₂ ^ (-4 : ℝ)) := by ring
              _ = 3 * π * (m₂ ^ (-(19 / 8) : ℝ) * m₂ ^ (-(11 / 8) : ℝ)) := by rw [e1]
              _ ≤ 3 * π * (m₂ ^ (-(19 / 8) : ℝ) * m₁ ^ (-(11 / 8) : ℝ)) := by gcongr
              _ = _ := by ring
    · have : ∀ b₂, pre1 (a₁, b₁) (a₂, b₂) = 0 := fun b₂ => by
        unfold pre1
        rw [indicator_of_notMem (show ((a₁, b₁), (a₂, b₂)) ∉
          {l : Form × Form | ‖l.1.1‖ ≤ ‖l.2.1‖} from h12)]
      simp [this]
  calc ∫⁻ l₂, pre1 (a₁, b₁) l₂ ≤ ∫⁻ a₂, ∫⁻ b₂, pre1 (a₁, b₁) (a₂, b₂) := by
        rw [Measure.volume_eq_prod]; exact lintegral_prod_le _
    _ ≤ ∫⁻ a₂, c₁ * ENNReal.ofReal (max 1 ‖a₂‖ ^ (-(19 / 8) : ℝ)) := lintegral_mono hinner
    _ = c₁ * Cphi := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **The half `|a₁| ≤ |a₂|` of the prefix integral is finite.** -/
theorem lintegral_pre1_lt_top : ∫⁻ l₁, ∫⁻ l₂, pre1 l₁ l₂ < ∞ := by
  set f : Form → ℝ≥0∞ :=
    rowSet.indicator (fun l => ENNReal.ofReal (3 * π * max 1 ‖l.1‖ ^ (-(11 / 8) : ℝ)))
  have hrow : ∀ a₁ : ℂ, ∫⁻ b₁, f (a₁, b₁) ≤
      ENNReal.ofReal (3 * π ^ 2) * ENNReal.ofReal (max 1 ‖a₁‖ ^ (-(19 / 8) : ℝ)) := by
    intro a₁
    set S := {b : ℂ | ‖b ^ 3‖ < 1 ∧ ‖a₁ * b ^ 2‖ < 1}
    have hS : MeasurableSet S :=
      (measurableSet_lt (f := fun b : ℂ => ‖b ^ 3‖) (by fun_prop) measurable_const).inter
        (measurableSet_lt (f := fun b : ℂ => ‖a₁ * b ^ 2‖) (by fun_prop) measurable_const)
    have e : (fun b₁ => f (a₁, b₁)) =
        S.indicator fun _ => ENNReal.ofReal (3 * π * max 1 ‖a₁‖ ^ (-(11 / 8) : ℝ)) := by
      funext b
      simp only [f, rowSet, S, indicator, mem_ofPred_eq]
    have hm : 0 < max 1 ‖a₁‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
    rw [e, lintegral_indicator_const hS]
    calc ENNReal.ofReal (3 * π * max 1 ‖a₁‖ ^ (-(11 / 8) : ℝ)) * volume S
        ≤ ENNReal.ofReal (3 * π * max 1 ‖a₁‖ ^ (-(11 / 8) : ℝ)) *
            ENNReal.ofReal (π * max 1 ‖a₁‖ ^ (-1 : ℝ)) := by
          gcongr; exact volume_prefix_le a₁
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show 3 * π * max 1 ‖a₁‖ ^ (-(11 / 8) : ℝ) * (π * max 1 ‖a₁‖ ^ (-1 : ℝ)) =
            3 * π ^ 2 * (max 1 ‖a₁‖ ^ (-(11 / 8) : ℝ) * max 1 ‖a₁‖ ^ (-1 : ℝ)) by ring,
            rpow_mul_rpow_eq hm (by norm_num : -(11 / 8 : ℝ) + -1 = -(19 / 8))]
  calc ∫⁻ l₁, ∫⁻ l₂, pre1 l₁ l₂ ≤ ∫⁻ l₁, f l₁ * Cphi :=
        lintegral_mono fun l₁ => lintegral_pre1_le l₁
    _ ≤ ∫⁻ a₁, ∫⁻ b₁, f (a₁, b₁) * Cphi := by
        rw [Measure.volume_eq_prod]; exact lintegral_prod_le _
    _ = ∫⁻ a₁, (∫⁻ b₁, f (a₁, b₁)) * Cphi :=
        lintegral_congr fun a₁ => lintegral_mul_const' _ _ Cphi_lt_top.ne
    _ ≤ ∫⁻ a₁, ENNReal.ofReal (3 * π ^ 2) *
          ENNReal.ofReal (max 1 ‖a₁‖ ^ (-(19 / 8) : ℝ)) * Cphi :=
        lintegral_mono fun a₁ => by gcongr; exact hrow a₁
    _ = ENNReal.ofReal (3 * π ^ 2) * Cphi * Cphi := by
        rw [lintegral_mul_const' _ _ Cphi_lt_top.ne, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rfl
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top Cphi_lt_top) Cphi_lt_top

/-! ### The prefix integral -/

/-- **The weighted prefix volume at position two is finite**:
`∫∫ V(l₁, l₂) 𝟙_{preSet}(l₁, l₂) dl₁ dl₂ < ∞`. -/
theorem lintegral_pre_lt_top : ∫⁻ l₁, ∫⁻ l₂, pre l₁ l₂ < ∞ := by
  have hpt : ∀ l₁ l₂, pre l₁ l₂ ≤ pre1 l₁ l₂ + pre1 l₂ l₁ := by
    intro l₁ l₂
    rcases le_total ‖l₁.1‖ ‖l₂.1‖ with h | h
    · unfold pre1
      rw [indicator_of_mem (show (l₁, l₂) ∈ {l : Form × Form | ‖l.1.1‖ ≤ ‖l.2.1‖} from h)]
      exact le_self_add
    · unfold pre1
      rw [indicator_of_mem (show (l₂, l₁) ∈ {l : Form × Form | ‖l.1.1‖ ≤ ‖l.2.1‖} from h),
        pre_comm]
      exact le_add_self
  have hm1 : ∀ l₁ : Form, Measurable fun l₂ => pre1 l₁ l₂ := fun l₁ =>
    measurable_pre1.comp measurable_prodMk_left
  have hm2 : Measurable fun l₁ : Form => ∫⁻ l₂, pre1 l₁ l₂ :=
    measurable_pre1.lintegral_prod_right'
  calc ∫⁻ l₁, ∫⁻ l₂, pre l₁ l₂ ≤ ∫⁻ l₁, ∫⁻ l₂, (pre1 l₁ l₂ + pre1 l₂ l₁) :=
        lintegral_mono fun l₁ => lintegral_mono fun l₂ => hpt l₁ l₂
    _ = (∫⁻ l₁, ∫⁻ l₂, pre1 l₁ l₂) + ∫⁻ l₁, ∫⁻ l₂, pre1 l₂ l₁ := by
        simp_rw [lintegral_add_left (hm1 _)]
        rw [lintegral_add_left hm2]
    _ = (∫⁻ l₁, ∫⁻ l₂, pre1 l₁ l₂) + ∫⁻ l₁, ∫⁻ l₂, pre1 l₁ l₂ := by
        congr 1
        exact lintegral_lintegral_swap (measurable_pre1.comp measurable_swap).aemeasurable
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨lintegral_pre1_lt_top, lintegral_pre1_lt_top⟩

end SLT.MiddlePositions.Two
