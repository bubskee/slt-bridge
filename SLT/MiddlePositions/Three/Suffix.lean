/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Defs
public import SLT.PositionFour.Downstream.Quadratic
public import SLT.PositionFour.Upstream.Coords

/-!
# The weighted one-form suffix kernel at position three

The note's Lemma "Weighted one-form suffix" (Section 3 of `complex_middle_positions.tex`). A suffix
form `l = (a, b)` of a row at position three has cube `(a³, a²b, ab², b³)`. The leading map keeps
`q₂ = ab²`, `q₃ = b³` (both `< 1` in modulus) and couples the two rows only through
`Q = q₁ = a²b`.

* `lintegral_suffixWeight_mul`: the weighted pushforward under `l ↦ a²b` has the density
  `kernelN3 Q = ∫ W₁(a, Q/a²) 𝟙_{suffix}(a, Q/a²) |a|^{-4} da`. This is the substitution `b = Q/a²`
  for fixed `a ≠ 0`, followed by Tonelli; it is an identity of `lintegral`s, in form coordinates.
* `kernelN3_le_small`, `kernelN3_le_large`: `N₃(Q) ≤ 3π |Q|^{-1}` for `0 < |Q| ≤ 1` and
  `N₃(Q) ≤ 3π |Q|^{-7/6}` for `|Q| ≥ 1`. The note computes `N₃` exactly; only these upper bounds
  are proved here.
* `lintegral_kernelN3_near_lt_top`, `lintegral_kernelN3_far_sq_lt_top`: hence `N₃` is integrable
  on `|Q| ≤ 1` and square integrable on `|Q| > 1`.
-/

@[expose] public section

namespace SLT.MiddlePositions.Three

open MeasureTheory Set Real Metric SLT.PositionFour SLT.PositionFour.Downstream
open scoped ENNReal NNReal

/-! ### The suffix constraints and weight -/

/-- The suffix constraints of one row at position three, `|q₂| = |a b²| < 1` and
`|q₃| = |b³| < 1`, for the suffix form `l = (a, b)`. -/
def suffixSet : Set Form := {l | ‖l.1 * l.2 ^ 2‖ < 1 ∧ ‖l.2 ^ 3‖ < 1}

/-- The suffix constraint set is measurable. -/
theorem measurableSet_suffixSet : MeasurableSet suffixSet :=
  (measurableSet_lt (f := fun l : Form => ‖l.1 * l.2 ^ 2‖) (by fun_prop) measurable_const).inter
    (measurableSet_lt (f := fun l : Form => ‖l.2 ^ 3‖) (by fun_prop) measurable_const)

/-- `W₁` is measurable. -/
theorem measurable_W1 : Measurable W1 := by unfold W1; fun_prop

/-- `W₁ ≥ 1`. -/
theorem one_le_W1 (l : Form) : 1 ≤ W1 l := by
  unfold W1; have := Real.rpow_nonneg (norm_nonneg l.1) (1 / 4 : ℝ)
  have := Real.rpow_nonneg (norm_nonneg l.2) (1 / 4 : ℝ); linarith

/-- The `W₁`-weighted indicator of the suffix constraints. -/
noncomputable def suffixWeight (l : Form) : ℝ≥0∞ :=
  suffixSet.indicator (fun l => ENNReal.ofReal (W1 l)) l

/-- The weighted suffix indicator is measurable. -/
theorem measurable_suffixWeight : Measurable suffixWeight :=
  measurable_W1.ennreal_ofReal.indicator measurableSet_suffixSet

/-! ### The kernel and the substitution `b = Q / a²` -/

/-- The one-form suffix kernel `N₃(Q) = ∫ W₁(a, Q/a²) 𝟙_{suffix}(a, Q/a²) |a|^{-4} da`. -/
noncomputable def kernelN3 (Q : ℂ) : ℝ≥0∞ := ∫⁻ a : ℂ, suffixWeight (a, Q / a ^ 2) * ‖a‖ₑ⁻¹ ^ 4

/-- The integrand of `kernelN3`, as a function of `(Q, a)`, is measurable. -/
theorem measurable_kernelN3_integrand :
    Measurable fun p : ℂ × ℂ => suffixWeight (p.2, p.1 / p.2 ^ 2) * ‖p.2‖ₑ⁻¹ ^ 4 :=
  (measurable_suffixWeight.comp (by fun_prop)).mul (by fun_prop)

/-- For fixed `Q`, the integrand of `kernelN3` is measurable in `a`. -/
theorem measurable_kernelN3_integrand_left (Q : ℂ) :
    Measurable fun a : ℂ => suffixWeight (a, Q / a ^ 2) * ‖a‖ₑ⁻¹ ^ 4 :=
  measurable_kernelN3_integrand.comp (measurable_const.prodMk measurable_id)

/-- For fixed `a`, `Q ↦ W₁(a, Q/a²) 𝟙(a, Q/a²) h(Q)` is measurable. -/
theorem measurable_suffixWeight_div_mul (a : ℂ) {h : ℂ → ℝ≥0∞} (hh : Measurable h) :
    Measurable fun Q : ℂ => suffixWeight (a, Q / a ^ 2) * h Q :=
  (measurable_suffixWeight.comp (measurable_const.prodMk (measurable_id.div_const _))).mul hh

/-- The kernel is measurable. -/
theorem measurable_kernelN3 : Measurable kernelN3 :=
  measurable_kernelN3_integrand.lintegral_prod_right'

/-- The real Jacobian of `b ↦ a² b` is `|a|⁴`. -/
theorem inv_ofReal_normSq_sq (a : ℂ) :
    (ENNReal.ofReal (Complex.normSq (a ^ 2)))⁻¹ = ‖a‖ₑ⁻¹ ^ 4 := by
  rw [Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul, ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm, ENNReal.inv_pow]

/-- **The weighted one-form pushforward.** For measurable `h ≥ 0` on `ℂ`,
`∫ W₁(l) 𝟙_{suffix}(l) h(a²b) dl = ∫ N₃(Q) h(Q) dQ`. -/
theorem lintegral_suffixWeight_mul {h : ℂ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ l : Form, suffixWeight l * h (l.1 ^ 2 * l.2) = ∫⁻ Q, kernelN3 Q * h Q := by
  have hm : Measurable fun l : Form => suffixWeight l * h (l.1 ^ 2 * l.2) :=
    measurable_suffixWeight.mul (hh.comp (by fun_prop))
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  have step : ∀ a : ℂ, a ≠ 0 → ∫⁻ b, suffixWeight (a, b) * h (a ^ 2 * b) =
      ∫⁻ Q, suffixWeight (a, Q / a ^ 2) * ‖a‖ₑ⁻¹ ^ 4 * h Q := by
    intro a ha
    have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
    have e : ∀ b, suffixWeight (a, b) * h (a ^ 2 * b) =
        (fun Q => suffixWeight (a, Q / a ^ 2) * h Q) (a ^ 2 * b) := by
      intro b; simp only; rw [mul_div_cancel_left₀ b ha2]
    rw [lintegral_congr e, lintegral_comp_mul_left (F := fun Q => suffixWeight (a, Q / a ^ 2) * h Q)
      ha2 (measurable_suffixWeight_div_mul a hh), inv_ofReal_normSq_sq,
      ← lintegral_const_mul _ (measurable_suffixWeight_div_mul a hh)]
    refine lintegral_congr fun Q => ?_
    ring
  have hm2 : Measurable fun p : ℂ × ℂ => suffixWeight (p.1, p.2 / p.1 ^ 2) * ‖p.1‖ₑ⁻¹ ^ 4 *
      h p.2 :=
    ((measurable_suffixWeight.comp (by fun_prop)).mul (by fun_prop)).mul (hh.comp measurable_snd)
  calc ∫⁻ a, ∫⁻ b, suffixWeight (a, b) * h ((a, b).1 ^ 2 * (a, b).2)
      = ∫⁻ a, ∫⁻ Q, suffixWeight (a, Q / a ^ 2) * ‖a‖ₑ⁻¹ ^ 4 * h Q := by
        refine lintegral_congr_ae ?_
        filter_upwards [Measure.ae_ne volume (0 : ℂ)] with a ha
        exact step a ha
    _ = ∫⁻ Q, ∫⁻ a, suffixWeight (a, Q / a ^ 2) * ‖a‖ₑ⁻¹ ^ 4 * h Q :=
        lintegral_lintegral_swap hm2.aemeasurable
    _ = ∫⁻ Q, kernelN3 Q * h Q := by
        refine lintegral_congr fun Q => ?_
        rw [kernelN3, lintegral_mul_const _ (measurable_kernelN3_integrand_left Q)]

/-! ### Pointwise bounds on the kernel -/

/-- The suffix constraints at `b = Q / a²`: `|Q|³ < |a|⁶` and `|Q|² < |a|³`. -/
theorem suffix_lower {a Q : ℂ} (ha : a ≠ 0) (hl : (a, Q / a ^ 2) ∈ suffixSet) :
    ‖Q‖ ^ 3 < ‖a‖ ^ 6 ∧ ‖Q‖ ^ 2 < ‖a‖ ^ 3 := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  obtain ⟨h1, h2⟩ := hl
  simp only [norm_mul, norm_pow, norm_div] at h1 h2
  constructor
  · rw [div_pow, ← pow_mul, div_lt_one (by positivity)] at h2; exact h2
  · rw [div_pow, ← pow_mul, mul_div_assoc', div_lt_one (by positivity),
      show ‖a‖ ^ (2 * 2) = ‖a‖ * ‖a‖ ^ 3 by ring] at h1
    exact lt_of_mul_lt_mul_left h1 hapos.le

/-- From `q^n < x^m` to `q^{n/m} < x`. -/
private lemma rpow_lt_of_pow_lt {q x : ℝ} (hq : 0 ≤ q) (hx : 0 < x) {n m : ℕ} (hm : 0 < m)
    (h : q ^ n < x ^ m) : q ^ ((n : ℝ) / m) < x := by
  by_contra hc
  replace hc := not_lt.mp hc
  have : (q ^ ((n : ℝ) / m)) ^ m = q ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq, div_mul_cancel₀ _ (by positivity),
      Real.rpow_natCast]
  have := pow_le_pow_left₀ hx.le hc m
  linarith

/-- The real form of the weighted integrand at `b = Q/a²`:
`W₁(a, Q/a²) |a|^{-4} = |a|^{-4} + |a|^{-15/4} + |Q|^{1/4} |a|^{-9/2}`. -/
private lemma weight_identity {x q : ℝ} (hx : 0 < x) (hq : 0 ≤ q) :
    (1 + x ^ (1 / 4 : ℝ) + (q / x ^ 2) ^ (1 / 4 : ℝ)) * x ^ (-4 : ℝ) =
      x ^ (-4 : ℝ) + x ^ (-(15 / 4) : ℝ) + q ^ (1 / 4 : ℝ) * x ^ (-(9 / 2) : ℝ) := by
  have h1 : (q / x ^ 2) ^ (1 / 4 : ℝ) = q ^ (1 / 4 : ℝ) * x ^ (-(1 / 2) : ℝ) := by
    rw [Real.div_rpow hq (by positivity), show (x ^ 2 : ℝ) = x ^ (2 : ℝ) by norm_cast,
      ← Real.rpow_mul hx.le, Real.rpow_neg hx.le, div_eq_mul_inv]
    norm_num
  rw [h1]
  calc (1 + x ^ (1 / 4 : ℝ) + q ^ (1 / 4 : ℝ) * x ^ (-(1 / 2) : ℝ)) * x ^ (-4 : ℝ)
      = x ^ (-4 : ℝ) + x ^ (1 / 4 : ℝ) * x ^ (-4 : ℝ) +
          q ^ (1 / 4 : ℝ) * (x ^ (-(1 / 2) : ℝ) * x ^ (-4 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hx, ← Real.rpow_add hx]; norm_num

/-- **The kernel below a threshold.** If the suffix constraints at `b = Q/a²` force `|a| > c`,
then `N₃(Q) ≤ π c^{-2} + (8π/7) c^{-7/4} + (4π/5) |Q|^{1/4} c^{-5/2}`. -/
theorem kernelN3_le_of_threshold {Q : ℂ} {c : ℝ} (hc : 0 < c)
    (hthr : ∀ a : ℂ, a ≠ 0 → (a, Q / a ^ 2) ∈ suffixSet → c < ‖a‖) :
    kernelN3 Q ≤ ENNReal.ofReal (π * c ^ (-2 : ℝ) + 8 * π / 7 * c ^ (-(7 / 4) : ℝ) +
      4 * π / 5 * (‖Q‖ ^ (1 / 4 : ℝ) * c ^ (-(5 / 2) : ℝ))) := by
  set S := {a : ℂ | c < ‖a‖}
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_norm
  have hpt : ∀ a : ℂ, a ≠ 0 → suffixWeight (a, Q / a ^ 2) * ‖a‖ₑ⁻¹ ^ 4 ≤
      S.indicator (fun a => ‖a‖ₑ⁻¹ ^ (4 : ℝ) + ‖a‖ₑ⁻¹ ^ (15 / 4 : ℝ) +
        ENNReal.ofReal (‖Q‖ ^ (1 / 4 : ℝ)) * ‖a‖ₑ⁻¹ ^ (9 / 2 : ℝ)) a := by
    intro a ha
    by_cases hl : (a, Q / a ^ 2) ∈ suffixSet
    · have haS : a ∈ S := hthr a ha hl
      have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
      rw [suffixWeight, indicator_of_mem hl, indicator_of_mem haS]
      refine le_of_eq ?_
      rw [show (‖a‖ₑ⁻¹ ^ 4 : ℝ≥0∞) = ‖a‖ₑ⁻¹ ^ (4 : ℝ) by
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast],
        enorm_inv_rpow_of_ne_zero ha, enorm_inv_rpow_of_ne_zero ha,
        enorm_inv_rpow_of_ne_zero ha, ← ENNReal.ofReal_mul (by unfold W1; positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      simp only [W1]
      rw [norm_div, norm_pow]
      exact weight_identity hapos (norm_nonneg Q)
    · rw [suffixWeight, indicator_of_notMem hl, zero_mul]; exact bot_le
  have hmG : ∀ γ : ℝ, Measurable fun a : ℂ => ‖a‖ₑ⁻¹ ^ γ := fun γ => by fun_prop
  calc kernelN3 Q ≤ ∫⁻ a, S.indicator (fun a => ‖a‖ₑ⁻¹ ^ (4 : ℝ) + ‖a‖ₑ⁻¹ ^ (15 / 4 : ℝ) +
        ENNReal.ofReal (‖Q‖ ^ (1 / 4 : ℝ)) * ‖a‖ₑ⁻¹ ^ (9 / 2 : ℝ)) a := by
        refine lintegral_mono_ae ?_
        filter_upwards [Measure.ae_ne volume (0 : ℂ)] with a ha
        exact hpt a ha
    _ = (∫⁻ a in S, ‖a‖ₑ⁻¹ ^ (4 : ℝ)) + (∫⁻ a in S, ‖a‖ₑ⁻¹ ^ (15 / 4 : ℝ)) +
          ENNReal.ofReal (‖Q‖ ^ (1 / 4 : ℝ)) * ∫⁻ a in S, ‖a‖ₑ⁻¹ ^ (9 / 2 : ℝ) := by
        rw [lintegral_indicator hS, lintegral_add_left (by fun_prop : Measurable fun a : ℂ =>
            ‖a‖ₑ⁻¹ ^ (4 : ℝ) + ‖a‖ₑ⁻¹ ^ (15 / 4 : ℝ)),
          lintegral_add_left (hmG _), lintegral_const_mul _ (hmG _)]
    _ = _ := by
        rw [lintegral_norm_gt_inv_rpow (by norm_num) hc,
          lintegral_norm_gt_inv_rpow (by norm_num) hc,
          lintegral_norm_gt_inv_rpow (by norm_num) hc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        norm_num
        ring

/-- `(q^a)^b = q^(a b)` for `q ≥ 0`, with the product exponent named. -/
private lemma rpow_rpow_of_mul {q a b c : ℝ} (hq : 0 ≤ q) (h : a * b = c) :
    (q ^ a) ^ b = q ^ c := by rw [← Real.rpow_mul hq, h]

/-- **Small `Q`**: `N₃(Q) ≤ 3π |Q|^{-1}` for `0 < |Q| ≤ 1`. -/
theorem kernelN3_le_small {Q : ℂ} (hQ0 : Q ≠ 0) (hQ1 : ‖Q‖ ≤ 1) :
    kernelN3 Q ≤ ENNReal.ofReal (3 * π * ‖Q‖ ^ (-1 : ℝ)) := by
  have hq : 0 < ‖Q‖ := norm_pos_iff.mpr hQ0
  set c := ‖Q‖ ^ (1 / 2 : ℝ) with hcdef
  have hc : 0 < c := Real.rpow_pos_of_pos hq _
  have hc1 : c ≤ 1 := Real.rpow_le_one hq.le hQ1 (by norm_num)
  refine (kernelN3_le_of_threshold hc fun a ha hl => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
  · have h := rpow_lt_of_pow_lt (norm_nonneg Q) (norm_pos_iff.mpr ha) (by norm_num : 0 < 6)
      (suffix_lower ha hl).1
    rw [hcdef]; convert h using 2; norm_num
  · have e1 : c ^ (-2 : ℝ) = ‖Q‖ ^ (-1 : ℝ) := rpow_rpow_of_mul hq.le (by norm_num)
    have e2 : c ^ (-(7 / 4) : ℝ) ≤ c ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hc hc1 (by norm_num)
    have e3 : ‖Q‖ ^ (1 / 4 : ℝ) * c ^ (-(5 / 2) : ℝ) = ‖Q‖ ^ (-1 : ℝ) := by
      rw [rpow_rpow_of_mul hq.le (show (1 / 2 : ℝ) * (-(5 / 2)) = -(5 / 4) by norm_num),
        ← Real.rpow_add hq]; norm_num
    rw [e3, e1] at *
    have hp : 0 ≤ ‖Q‖ ^ (-1 : ℝ) := by positivity
    have := Real.pi_pos
    nlinarith

/-- **Large `Q`**: `N₃(Q) ≤ 3π |Q|^{-7/6}` for `|Q| ≥ 1`. -/
theorem kernelN3_le_large {Q : ℂ} (hQ1 : 1 ≤ ‖Q‖) :
    kernelN3 Q ≤ ENNReal.ofReal (3 * π * ‖Q‖ ^ (-(7 / 6) : ℝ)) := by
  have hq : 0 < ‖Q‖ := one_pos.trans_le hQ1
  set c := ‖Q‖ ^ (2 / 3 : ℝ) with hcdef
  have hc : 0 < c := Real.rpow_pos_of_pos hq _
  have hc1 : 1 ≤ c := Real.one_le_rpow hQ1 (by norm_num)
  refine (kernelN3_le_of_threshold hc fun a ha hl => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
  · have h := rpow_lt_of_pow_lt (norm_nonneg Q) (norm_pos_iff.mpr ha) (by norm_num : 0 < 3)
      (suffix_lower ha hl).2
    rw [hcdef]; convert h using 2
  · have e1 : c ^ (-2 : ℝ) ≤ c ^ (-(7 / 4) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have e2 : c ^ (-(7 / 4) : ℝ) = ‖Q‖ ^ (-(7 / 6) : ℝ) := rpow_rpow_of_mul hq.le (by norm_num)
    have e3 : ‖Q‖ ^ (1 / 4 : ℝ) * c ^ (-(5 / 2) : ℝ) ≤ ‖Q‖ ^ (-(7 / 6) : ℝ) := by
      rw [rpow_rpow_of_mul hq.le (show (2 / 3 : ℝ) * (-(5 / 2)) = -(5 / 3) by norm_num),
        ← Real.rpow_add hq]
      exact Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
    rw [e2] at e1
    have hp : 0 ≤ ‖Q‖ ^ (-(7 / 6) : ℝ) := by positivity
    have := Real.pi_pos
    nlinarith

/-! ### Integrability near `0`, square integrability near `∞` -/

/-- The near part: `∫_{|Q| ≤ 1} N₃ < ∞`. -/
theorem lintegral_kernelN3_near_lt_top : ∫⁻ Q in closedBall (0 : ℂ) 1, kernelN3 Q < ∞ := by
  have hpt : ∀ᵐ Q : ℂ, Q ∈ closedBall (0 : ℂ) 1 →
      kernelN3 Q ≤ ENNReal.ofReal (3 * π) * ‖Q‖ₑ⁻¹ ^ (1 : ℝ) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with Q hQ hQ1
    rw [mem_closedBall_zero_iff] at hQ1
    rw [enorm_inv_rpow_of_ne_zero hQ, ← ENNReal.ofReal_mul (by positivity)]
    exact kernelN3_le_small hQ hQ1
  calc ∫⁻ Q in closedBall (0 : ℂ) 1, kernelN3 Q
      ≤ ∫⁻ Q in closedBall (0 : ℂ) 1, ENNReal.ofReal (3 * π) * ‖Q‖ₑ⁻¹ ^ (1 : ℝ) :=
        setLIntegral_mono_ae (by fun_prop) hpt
    _ ≤ ∫⁻ Q in ball (0 : ℂ) 2, ENNReal.ofReal (3 * π) * ‖Q‖ₑ⁻¹ ^ (1 : ℝ) :=
        lintegral_mono_set (closedBall_subset_ball (by norm_num))
    _ = ENNReal.ofReal (3 * π) * ∫⁻ Q in ball (0 : ℂ) 2, ‖Q‖ₑ⁻¹ ^ (1 : ℝ) :=
        lintegral_const_mul _ (by fun_prop)
    _ < ∞ := by
        rw [lintegral_ball_inv_rpow (by norm_num) (by norm_num)]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- The far part: `∫_{|Q| > 1} N₃² < ∞`. -/
theorem lintegral_kernelN3_far_sq_lt_top : ∫⁻ Q in {Q : ℂ | 1 < ‖Q‖}, kernelN3 Q ^ 2 < ∞ := by
  have hpt : ∀ Q ∈ {Q : ℂ | 1 < ‖Q‖},
      kernelN3 Q ^ 2 ≤ ENNReal.ofReal ((3 * π) ^ 2) * ‖Q‖ₑ⁻¹ ^ (7 / 3 : ℝ) := by
    intro Q hQ
    have hQ1 : 1 ≤ ‖Q‖ := le_of_lt hQ
    have hq : 0 < ‖Q‖ := one_pos.trans_le hQ1
    rw [enorm_inv_rpow_of_ne_zero (norm_pos_iff.mp hq), ← ENNReal.ofReal_mul (by positivity)]
    calc kernelN3 Q ^ 2 ≤ ENNReal.ofReal (3 * π * ‖Q‖ ^ (-(7 / 6) : ℝ)) ^ 2 :=
          pow_le_pow_left₀ bot_le (kernelN3_le_large hQ1) 2
      _ = _ := by
          rw [← ENNReal.ofReal_pow (by positivity)]
          congr 1
          rw [mul_pow, ← Real.rpow_natCast (‖Q‖ ^ _), ← Real.rpow_mul hq.le]
          norm_num
  have hS : MeasurableSet {Q : ℂ | 1 < ‖Q‖} := measurableSet_lt measurable_const measurable_norm
  calc ∫⁻ Q in {Q : ℂ | 1 < ‖Q‖}, kernelN3 Q ^ 2
      ≤ ∫⁻ Q in {Q : ℂ | 1 < ‖Q‖}, ENNReal.ofReal ((3 * π) ^ 2) * ‖Q‖ₑ⁻¹ ^ (7 / 3 : ℝ) :=
        setLIntegral_mono (by fun_prop) hpt
    _ = ENNReal.ofReal ((3 * π) ^ 2) * ∫⁻ Q in {Q : ℂ | 1 < ‖Q‖}, ‖Q‖ₑ⁻¹ ^ (7 / 3 : ℝ) :=
        lintegral_const_mul _ (by fun_prop)
    _ < ∞ := by
        rw [lintegral_norm_gt_inv_rpow (by norm_num) one_pos]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

end SLT.MiddlePositions.Three
