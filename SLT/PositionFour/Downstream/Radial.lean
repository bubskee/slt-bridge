/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Radial integrals on `ℂ`

The one-variable analytic input of Lemma 1 of `complex_position_four.tex`. Everything is a
`lintegral` of an inverse power of a distance in the plane:

* `lintegral_norm_comp`: polar coordinates for a radial function, `∫ g(|z|) = 2π ∫₀^∞ r g(r) dr`;
* `lintegral_ball_inv_rpow`: `∫_{|z| < R} |z|^{-s} = 2π R^{2-s} / (2 - s)` for `s < 2`;
* `lintegral_ball_sub_inv_rpow_le`: the same bound, with `π R^{2-s}` added, for an off-centre pole
  `|z - c|^{-s}` (uniform in `c`);
* `lintegral_norm_gt_inv_rpow`: `∫_{|z| > c} |z|^{-γ} = 2π c^{2-γ} / (γ - 2)` for `γ > 2`.

Inverse powers are written `‖z‖ₑ⁻¹ ^ s` in `ℝ≥0∞`, the convention of `densityBound`; at `z = 0`
this is `∞` for `s > 0`.
-/

@[expose] public section

namespace SLT.PositionFour

open MeasureTheory Set Real Metric
open scoped ENNReal NNReal

/-- **Polar coordinates for a radial function on `ℂ`**:
`∫ g(|z|) dz = 2π ∫_{r > 0} r g(r) dr`. -/
theorem lintegral_norm_comp {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z : ℂ, g ‖z‖ = ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * g r := by
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  simp only [Complex.norm_polarCoord_symm, smul_eq_mul]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ (by
      exact ((measurable_fst.ennreal_ofReal).mul (hg.comp (continuous_abs.measurable.comp
        measurable_fst))).aemeasurable)]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
  simp only [abs_of_pos hr]
  rw [setLIntegral_const, Real.volume_Ioo, mul_comm]
  congr 1; ring_nf

/-- `r · r^{-s} = r^{1-s}` in `ℝ≥0∞`, for `r > 0`. -/
private lemma ofReal_mul_inv_rpow {r s : ℝ} (hr : 0 < r) :
    ENNReal.ofReal r * (ENNReal.ofReal r)⁻¹ ^ s = ENNReal.ofReal (r ^ (1 - s)) := by
  rw [← ENNReal.ofReal_inv_of_pos hr, ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hr),
    ← ENNReal.ofReal_mul hr.le, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, sub_eq_add_neg,
    Real.rpow_add hr, Real.rpow_one]

/-- **The centred ball integral**: `∫_{|z| < R} |z|^{-s} dz = 2π R^{2-s} / (2 - s)` for `s < 2`. -/
theorem lintegral_ball_inv_rpow {s R : ℝ} (hs : s < 2) (hR : 0 < R) :
    ∫⁻ z in ball (0 : ℂ) R, ‖z‖ₑ⁻¹ ^ s = ENNReal.ofReal (2 * π * (R ^ (2 - s) / (2 - s))) := by
  set g : ℝ → ℝ≥0∞ := (Iio R).indicator fun r => (ENNReal.ofReal r)⁻¹ ^ s
  have hg : Measurable g :=
    (ENNReal.measurable_ofReal.inv.pow_const s).indicator measurableSet_Iio
  have hcongr : (fun z : ℂ => (ball (0 : ℂ) R).indicator (fun z => ‖z‖ₑ⁻¹ ^ s) z) =
      fun z => g ‖z‖ := by
    funext z
    simp only [g, indicator, mem_ball_zero_iff, mem_Iio, ofReal_norm]
  rw [← lintegral_indicator measurableSet_ball, hcongr, lintegral_norm_comp hg,
    ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * π by positivity)]
  congr 1
  have h1 : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r * g r =
      (Iio R).indicator (fun r => ENNReal.ofReal (r ^ (1 - s))) r := by
    intro r hr
    by_cases hrR : r < R
    · simp only [g, indicator_of_mem (show r ∈ Iio R from hrR)]
      exact ofReal_mul_inv_rpow hr
    · simp [g, indicator_of_notMem (show r ∉ Iio R from hrR)]
  rw [setLIntegral_congr_fun measurableSet_Ioi h1, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
  have hint : IntegrableOn (fun r : ℝ => r ^ (1 - s)) (Ioo 0 R) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hR).mpr (by linarith)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioo fun r hr => Real.rpow_nonneg hr.1.le _),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le,
    integral_rpow (Or.inl (by linarith))]
  congr 1
  rw [Real.zero_rpow (by linarith)]
  ring_nf

/-- **The off-centre ball integral**, uniform in the pole `c`: for `0 ≤ s < 2`,
`∫_{|z| < R} |z - c|^{-s} dz ≤ (2π/(2-s) + π) R^{2-s}`. The part of the translated ball inside
`|w| < R` is the centred integral; outside it `|w|^{-s} ≤ R^{-s}` on a set of area `π R²`. -/
theorem lintegral_ball_sub_inv_rpow_le (c : ℂ) {s R : ℝ} (hs0 : 0 ≤ s) (hs : s < 2)
    (hR : 0 < R) :
    ∫⁻ z in ball (0 : ℂ) R, ‖z - c‖ₑ⁻¹ ^ s ≤
      ENNReal.ofReal ((2 * π / (2 - s) + π) * R ^ (2 - s)) := by
  -- translate the pole to the origin
  have htr : ∫⁻ z in ball (0 : ℂ) R, ‖z - c‖ₑ⁻¹ ^ s =
      ∫⁻ w in ball (-c) R, ‖w‖ₑ⁻¹ ^ s := by
    rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball,
      ← lintegral_add_right_eq_self _ c]
    refine lintegral_congr fun w => ?_
    simp only [indicator, mem_ball, dist_eq_norm, sub_neg_eq_add]
    simp [add_sub_cancel_right]
  rw [htr]
  -- split at `|w| = R`
  have hpt : ∀ w : ℂ, (ball (-c) R).indicator (fun w => ‖w‖ₑ⁻¹ ^ s) w ≤
      (ball (0 : ℂ) R).indicator (fun w => ‖w‖ₑ⁻¹ ^ s) w +
        (ball (-c) R).indicator (fun _ => (ENNReal.ofReal R)⁻¹ ^ s) w := by
    intro w
    by_cases hw : w ∈ ball (-c) R
    · rw [indicator_of_mem hw, indicator_of_mem hw]
      by_cases hw0 : w ∈ ball (0 : ℂ) R
      · rw [indicator_of_mem hw0]; exact le_self_add
      · rw [indicator_of_notMem hw0, zero_add]
        rw [mem_ball_zero_iff, not_lt] at hw0
        refine ENNReal.rpow_le_rpow ?_ hs0
        rw [← ofReal_norm]
        exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hw0)
    · rw [indicator_of_notMem hw]; exact bot_le
  have hm1 : Measurable ((ball (0 : ℂ) R).indicator fun w : ℂ => ‖w‖ₑ⁻¹ ^ s) :=
    (by fun_prop : Measurable fun w : ℂ => ‖w‖ₑ⁻¹ ^ s).indicator measurableSet_ball
  have hA := lintegral_ball_inv_rpow hs hR
  rw [← lintegral_indicator measurableSet_ball] at hA
  have hB : ∫⁻ w, (ball (-c) R).indicator (fun _ => (ENNReal.ofReal R)⁻¹ ^ s) w =
      ENNReal.ofReal (π * R ^ (2 - s)) := by
    rw [lintegral_indicator measurableSet_ball, setLIntegral_const, Complex.volume_ball,
      ← ENNReal.ofReal_inv_of_pos hR, ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hR),
      ← ENNReal.ofReal_pow hR.le, show ((NNReal.pi : ℝ≥0∞)) = ENNReal.ofReal π by
        rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi],
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.inv_rpow hR.le, ← Real.rpow_neg hR.le, ← Real.rpow_natCast,
      show (2 : ℝ) - s = -s + ((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_add hR]
    ring
  rw [← lintegral_indicator measurableSet_ball]
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_left hm1, hA, hB, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have : (2 - s) ≠ 0 := by linarith
  field_simp

/-- **The tail integral**: `∫_{|z| > c} |z|^{-γ} dz = 2π c^{2-γ} / (γ - 2)` for `γ > 2`, `c > 0`. -/
theorem lintegral_norm_gt_inv_rpow {γ c : ℝ} (hγ : 2 < γ) (hc : 0 < c) :
    ∫⁻ z in {z : ℂ | c < ‖z‖}, ‖z‖ₑ⁻¹ ^ γ =
      ENNReal.ofReal (2 * π * (c ^ (2 - γ) / (γ - 2))) := by
  set g : ℝ → ℝ≥0∞ := (Ioi c).indicator fun r => (ENNReal.ofReal r)⁻¹ ^ γ
  have hg : Measurable g :=
    (ENNReal.measurable_ofReal.inv.pow_const γ).indicator measurableSet_Ioi
  have hm : MeasurableSet {z : ℂ | c < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hcongr : (fun z : ℂ => {z : ℂ | c < ‖z‖}.indicator (fun z => ‖z‖ₑ⁻¹ ^ γ) z) =
      fun z => g ‖z‖ := by
    funext z
    simp only [g, indicator, mem_ofPred_eq, mem_Ioi, ofReal_norm]
  rw [← lintegral_indicator hm, hcongr, lintegral_norm_comp hg,
    ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * π by positivity)]
  congr 1
  have h1 : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r * g r =
      (Ioi c).indicator (fun r => ENNReal.ofReal (r ^ (1 - γ))) r := by
    intro r hr
    by_cases hrc : c < r
    · simp only [g, indicator_of_mem (show r ∈ Ioi c from hrc)]
      exact ofReal_mul_inv_rpow hr
    · simp [g, indicator_of_notMem (show r ∉ Ioi c from hrc)]
  rw [setLIntegral_congr_fun measurableSet_Ioi h1, lintegral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_left.mpr hc.le]
  have hint : IntegrableOn (fun r : ℝ => r ^ (1 - γ)) (Ioi c) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioi fun r (hr : c < r) =>
      Real.rpow_nonneg (hc.trans hr).le _), integral_Ioi_rpow_of_lt (by linarith) hc]
  congr 1
  have : (1 - γ + 1) = -(γ - 2) := by ring
  rw [this, show 2 - γ = -(γ - 2) by ring]
  have : (γ - 2) ≠ 0 := by linarith
  field_simp

end SLT.PositionFour
