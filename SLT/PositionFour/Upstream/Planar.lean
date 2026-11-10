/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Power singularities on the complex plane

Planar integrability facts used by the reference integral and by local finiteness:

* `lintegral_ball_rpow_neg_lt_top`: `∫_{|z| < r} |z|^{-p} < ∞` for `p < 2`;
* `lintegral_one_add_rpow_neg_lt_top`: `∫_ℂ (1 + |z|)^{-q} < ∞` for `q > 2`;
* `lintegral_twoPoint_lt_top`: `∫_ℂ |z - a|^{-p} |z - b|^{-q} (1 + |z|)^c < ∞` for `a ≠ b`,
  `p, q < 2`, `c ≥ 0` and `p + q - c > 2`.

Singular weights are `ℝ≥0∞`-valued (`‖z‖ₑ ^ (-p)`, which is `∞` at `z = 0`); the proofs go through
real-valued integrability and agree with it off a null set.
-/

@[expose] public section

namespace SLT.PositionFour

open MeasureTheory Set Metric
open scoped ENNReal

/-- `‖z‖ₑ ^ (-p) = ofReal (‖z‖ ^ (-p))` away from `0`. -/
theorem enorm_rpow_eq_ofReal {z : ℂ} (hz : z ≠ 0) (p : ℝ) :
    ‖z‖ₑ ^ p = ENNReal.ofReal (‖z‖ ^ p) := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr hz)]

/-- `|z|^{-p}` is integrable on a ball of `ℂ` for `p < 2` (real-valued form). -/
theorem integrableOn_ball_rpow_neg {p : ℝ} (hp : p < 2) (r : ℝ) :
    IntegrableOn (fun z : ℂ => ‖z‖ ^ (-p)) (ball 0 r) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.mpr hr]; exact integrableOn_empty
  rw [integrableOn_fun_norm_addHaar volume (f := fun y : ℝ => y ^ (-p)),
    Complex.finrank_real_complex]
  have h : IntegrableOn (fun y : ℝ => y ^ (1 - p)) (Ioo 0 r) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hr).mpr (by linarith)
  refine h.congr_fun (fun y hy => ?_) measurableSet_Ioo
  simp only [smul_eq_mul]
  rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one, Real.rpow_sub hy.1, Real.rpow_one,
    Real.rpow_neg hy.1.le, div_eq_mul_inv]

/-- `∫_{|z| < r} |z|^{-p} < ∞` for `p < 2`. -/
theorem lintegral_ball_rpow_neg_lt_top {p : ℝ} (hp : p < 2) (r : ℝ) :
    ∫⁻ z in ball (0 : ℂ) r, ‖z‖ₑ ^ (-p) < ∞ := by
  have h := (integrableOn_ball_rpow_neg hp r).setLIntegral_lt_top
  refine lt_of_eq_of_lt (setLIntegral_congr_fun_ae measurableSet_ball ?_) h
  filter_upwards [Measure.ae_ne volume (0 : ℂ)] with z hz _
  exact enorm_rpow_eq_ofReal hz _

/-- `∫_ℂ (1 + |z|)^{-q} < ∞` for `q > 2`. -/
theorem lintegral_one_add_rpow_neg_lt_top {q : ℝ} (hq : 2 < q) :
    ∫⁻ z : ℂ, ENNReal.ofReal ((1 + ‖z‖) ^ (-q)) < ∞ :=
  (integrable_one_add_norm (by rwa [Complex.finrank_real_complex, Nat.cast_ofNat])).lintegral_lt_top

/-- The translated ball singularity `1_{|z - a| < δ} |z - a|^{-p}` is integrable for `p < 2`. -/
theorem integrable_indicator_ball_rpow_neg {p : ℝ} (hp : p < 2) (a : ℂ) (δ : ℝ) :
    Integrable ((ball a δ).indicator fun z : ℂ => ‖z - a‖ ^ (-p)) := by
  have h :=
    ((integrableOn_ball_rpow_neg hp δ).integrable_indicator measurableSet_ball).comp_sub_right a
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [indicator, mem_ball, dist_eq_norm, sub_zero]

/-- **Two singular points.** For `a ≠ b`, `p, q < 2`, `c ≥ 0` and `p + q - c > 2`,
`∫_ℂ |z - a|^{-p} |z - b|^{-q} (1 + |z|)^c < ∞`. -/
theorem lintegral_twoPoint_lt_top {a b : ℂ} (hab : a ≠ b) {p q c : ℝ} (hp : p < 2)
    (hq : q < 2) (hc : 0 ≤ c) (hpqc : 2 < p + q - c) :
    ∫⁻ z : ℂ, ‖z - a‖ₑ ^ (-p) * ‖z - b‖ₑ ^ (-q) * ENNReal.ofReal ((1 + ‖z‖) ^ c) < ∞ := by
  set δ := ‖a - b‖ / 2 with hδ
  have hδ0 : 0 < δ := by have := norm_pos_iff.mpr (sub_ne_zero.mpr hab); positivity
  set κa := δ / (1 + ‖a‖ + δ)
  set κb := δ / (1 + ‖b‖ + δ)
  have hκa : 0 < κa := by positivity
  have hκb : 0 < κb := by positivity
  set C1 := δ ^ (-q) * (1 + ‖a‖ + δ) ^ c
  set C2 := δ ^ (-p) * (1 + ‖b‖ + δ) ^ c
  set C3 := κa ^ (-p) * κb ^ (-q)
  set G : ℂ → ℝ := fun z => C1 * (ball a δ).indicator (fun z => ‖z - a‖ ^ (-p)) z +
    C2 * (ball b δ).indicator (fun z => ‖z - b‖ ^ (-q)) z + C3 * (1 + ‖z‖) ^ (-(p + q - c))
  have hG : Integrable G :=
    (((integrable_indicator_ball_rpow_neg hp a δ).const_mul C1).add
      ((integrable_indicator_ball_rpow_neg hq b δ).const_mul C2)).add
      ((integrable_one_add_norm
        (by rw [Complex.finrank_real_complex]; push_cast; linarith)).const_mul C3)
  -- the pointwise bound off `{a, b}`
  have key : ∀ z : ℂ, z ≠ a → z ≠ b →
      ‖z - a‖ ^ (-p) * ‖z - b‖ ^ (-q) * (1 + ‖z‖) ^ c ≤ G z := by
    intro z hza hzb
    have hA : 0 < ‖z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hza)
    have hB : 0 < ‖z - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzb)
    have h1 : 0 ≤ C1 * (ball a δ).indicator (fun z => ‖z - a‖ ^ (-p)) z := by
      unfold indicator; split_ifs <;> positivity
    have h2 : 0 ≤ C2 * (ball b δ).indicator (fun z => ‖z - b‖ ^ (-q)) z := by
      unfold indicator; split_ifs <;> positivity
    have h3 : 0 ≤ C3 * (1 + ‖z‖) ^ (-(p + q - c)) := by positivity
    have hab' : ‖a - b‖ ≤ ‖z - a‖ + ‖z - b‖ := by
      calc ‖a - b‖ = ‖(z - b) - (z - a)‖ := by congr 1; ring
        _ ≤ ‖z - b‖ + ‖z - a‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    have hza' : ‖z‖ ≤ ‖a‖ + ‖z - a‖ := by
      calc ‖z‖ = ‖a + (z - a)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    have hzb' : ‖z‖ ≤ ‖b‖ + ‖z - b‖ := by
      calc ‖z‖ = ‖b + (z - b)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    by_cases hzA : z ∈ ball a δ
    · have hzA' : ‖z - a‖ < δ := by rwa [mem_ball, dist_eq_norm] at hzA
      have hBδ : δ ≤ ‖z - b‖ := by linarith
      have e1 : ‖z - b‖ ^ (-q) ≤ δ ^ (-q) := Real.rpow_le_rpow_of_nonpos hδ0 hBδ (by linarith)
      have e2 : (1 + ‖z‖) ^ c ≤ (1 + ‖a‖ + δ) ^ c :=
        Real.rpow_le_rpow (by positivity) (by linarith) hc
      have : ‖z - a‖ ^ (-p) * ‖z - b‖ ^ (-q) * (1 + ‖z‖) ^ c ≤
          C1 * (ball a δ).indicator (fun z => ‖z - a‖ ^ (-p)) z := by
        rw [indicator_of_mem hzA]
        calc ‖z - a‖ ^ (-p) * ‖z - b‖ ^ (-q) * (1 + ‖z‖) ^ c
            ≤ ‖z - a‖ ^ (-p) * δ ^ (-q) * (1 + ‖a‖ + δ) ^ c := by gcongr
          _ = _ := by ring
      linarith
    by_cases hzB : z ∈ ball b δ
    · have hzB' : ‖z - b‖ < δ := by rwa [mem_ball, dist_eq_norm] at hzB
      have hAδ : δ ≤ ‖z - a‖ := by linarith
      have e1 : ‖z - a‖ ^ (-p) ≤ δ ^ (-p) := Real.rpow_le_rpow_of_nonpos hδ0 hAδ (by linarith)
      have e2 : (1 + ‖z‖) ^ c ≤ (1 + ‖b‖ + δ) ^ c :=
        Real.rpow_le_rpow (by positivity) (by linarith) hc
      have : ‖z - a‖ ^ (-p) * ‖z - b‖ ^ (-q) * (1 + ‖z‖) ^ c ≤
          C2 * (ball b δ).indicator (fun z => ‖z - b‖ ^ (-q)) z := by
        rw [indicator_of_mem hzB]
        calc ‖z - a‖ ^ (-p) * ‖z - b‖ ^ (-q) * (1 + ‖z‖) ^ c
            ≤ δ ^ (-p) * ‖z - b‖ ^ (-q) * (1 + ‖b‖ + δ) ^ c := by gcongr
          _ = _ := by ring
      linarith
    · have hAδ : δ ≤ ‖z - a‖ := by
        rw [mem_ball, dist_eq_norm, not_lt] at hzA; exact hzA
      have hBδ : δ ≤ ‖z - b‖ := by
        rw [mem_ball, dist_eq_norm, not_lt] at hzB; exact hzB
      have hz1 : 0 < 1 + ‖z‖ := by positivity
      -- `|z - a| ≥ κa (1 + |z|)`
      have fa : κa * (1 + ‖z‖) ≤ ‖z - a‖ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right hAδ (by positivity : (0 : ℝ) ≤ 1 + ‖a‖),
          mul_le_mul_of_nonneg_left hza' hδ0.le, mul_le_mul_of_nonneg_left hAδ hδ0.le]
      have fb : κb * (1 + ‖z‖) ≤ ‖z - b‖ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right hBδ (by positivity : (0 : ℝ) ≤ 1 + ‖b‖),
          mul_le_mul_of_nonneg_left hzb' hδ0.le, mul_le_mul_of_nonneg_left hBδ hδ0.le]
      have ea : ‖z - a‖ ^ (-p) ≤ κa ^ (-p) * (1 + ‖z‖) ^ (-p) := by
        rw [← Real.mul_rpow hκa.le hz1.le]
        exact Real.rpow_le_rpow_of_nonpos (by positivity) fa (by linarith)
      have eb : ‖z - b‖ ^ (-q) ≤ κb ^ (-q) * (1 + ‖z‖) ^ (-q) := by
        rw [← Real.mul_rpow hκb.le hz1.le]
        exact Real.rpow_le_rpow_of_nonpos (by positivity) fb (by linarith)
      have : ‖z - a‖ ^ (-p) * ‖z - b‖ ^ (-q) * (1 + ‖z‖) ^ c ≤
          C3 * (1 + ‖z‖) ^ (-(p + q - c)) := by
        calc ‖z - a‖ ^ (-p) * ‖z - b‖ ^ (-q) * (1 + ‖z‖) ^ c
            ≤ (κa ^ (-p) * (1 + ‖z‖) ^ (-p)) * (κb ^ (-q) * (1 + ‖z‖) ^ (-q)) * (1 + ‖z‖) ^ c := by
              gcongr
          _ = C3 * ((1 + ‖z‖) ^ (-p) * (1 + ‖z‖) ^ (-q) * (1 + ‖z‖) ^ c) := by ring
          _ = C3 * (1 + ‖z‖) ^ (-(p + q - c)) := by
              rw [← Real.rpow_add hz1, ← Real.rpow_add hz1]; congr 2; ring
      linarith
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hG.lintegral_lt_top
  filter_upwards [Measure.ae_ne volume a, Measure.ae_ne volume b] with z hza hzb
  rw [enorm_rpow_eq_ofReal (sub_ne_zero.mpr hza), enorm_rpow_eq_ofReal (sub_ne_zero.mpr hzb),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (key z hza hzb)

end SLT.PositionFour
