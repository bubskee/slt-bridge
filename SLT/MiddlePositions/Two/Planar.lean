/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Toolkit.Quadratic
public import SLT.PositionFour.Downstream.Marginal

/-!
# Planar estimates for position two

Section 2 of `complex_middle_positions.tex` (Lemma "Planar powers and quadratics"), the parts that
position two needs beyond the interface `FullPlaneQuadratic` (the shifted-disc bound
`setLIntegral_ball_inv_rpow_le` and the tail power `lintegral_max_one_rpow_neg_lt_top` are in
`SLT/Pushforward/Radial.lean`):

* `lintegral_inv_quadratic_le`: the note's `eq:quad0` in completed-square form,
  `∫_ℂ |A((z - c)² - δ)|^{-t} ≤ K 4^{1-t} |A|^{-t} |δ|^{1-t}`, read off `FullPlaneQuadratic`;
* `lintegral_rpow_mul_inv_quadratic_le`: the note's `eq:quadw`,
  `∫_ℂ |z|^γ |A((z - c)² - δ)|^{-t} ≤ M |A|^{-t} |δ|^{1-t} (|c|^γ + |δ|^{γ/2})`
  for `1 < t`, `0 ≤ γ ≤ 1`, `γ < 2t - 2`.

The note writes `δ = d²`; here `δ` itself is the parameter, so no square root of a complex number
is chosen. The note proves `eq:quadw` from a reference integral and an affine substitution. Here
it is proved by splitting the plane at `|z - c| = 2|δ|^{1/2}`: inside, `|z|^γ` is bounded and
`eq:quad0` applies; outside, `|(z - c)² - δ| ≥ (3/4)|z - c|²` and the tail power bound applies.
-/

@[expose] public section

namespace SLT.MiddlePositions.Two

open MeasureTheory Set Real Metric SLT.PositionFour SLT.PositionFour.Downstream SLT.Pushforward
open scoped ENNReal NNReal

/-! ### Real powers -/

/-- `x^a x^b = x^c` for `x > 0` and `a + b = c`. -/
theorem rpow_mul_rpow_eq {x : ℝ} (hx : 0 < x) {a b c : ℝ} (h : a + b = c) :
    x ^ a * x ^ b = x ^ c := by rw [← Real.rpow_add hx, h]

/-- The completed-square scaling identity:
`(x²)^{-t} (4y³/x⁴)^{1-t} = 4^{1-t} x^{2t-4} y^{3-3t}` for `x, y > 0`. -/
theorem sq_rpow_mul_rpow_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    (x ^ 2) ^ (-t) * (4 * y ^ 3 / x ^ 4) ^ (1 - t) =
      4 ^ (1 - t) * x ^ (2 * t - 4) * y ^ (3 - 3 * t) := by
  have hx2 : (x ^ 2) ^ (-t) = x ^ (-(2 * t)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; congr 1; push_cast; ring
  have hy3 : (y ^ 3) ^ (1 - t) = y ^ (3 - 3 * t) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]; congr 1; push_cast; ring
  have hx4 : (x ^ 4) ^ (1 - t) = x ^ (4 - 4 * t) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; congr 1; push_cast; ring
  have hsplit : x ^ (-(2 * t)) = x ^ (2 * t - 4) * x ^ (4 - 4 * t) :=
    (rpow_mul_rpow_eq hx (by ring)).symm
  rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) (by positivity),
    hx2, hy3, hx4, hsplit]
  have : 0 < x ^ (4 - 4 * t) := by positivity
  field_simp

/-! ### Quadratics on the full plane -/

/-- **The completed-square form of `eq:quad0`**: for `A, δ ≠ 0`,
`∫_ℂ |A((z - c)² - δ)|^{-t} ≤ K 4^{1-t} |A|^{-t} |δ|^{1-t}`. -/
theorem lintegral_inv_quadratic_le {t K : ℝ} (hK : FullPlaneQuadratic t K) (hK0 : 0 ≤ K)
    {A c δ : ℂ} (hA : A ≠ 0) (hδ : δ ≠ 0) :
    ∫⁻ z, ‖A * ((z - c) ^ 2 - δ)‖ₑ⁻¹ ^ t ≤
      ENNReal.ofReal (K * 4 ^ (1 - t) * ‖A‖ ^ (-t) * ‖δ‖ ^ (1 - t)) := by
  have e : ∀ z : ℂ, A * ((z - c) ^ 2 - δ) = A * z ^ 2 + (-2 * A * c) * z + (A * c ^ 2 - A * δ) :=
    fun z => by ring
  simp_rw [e]
  refine (hK A _ _ hA).trans (le_of_eq ?_)
  have hd : (-2 * A * c) ^ 2 - 4 * A * (A * c ^ 2 - A * δ) = 4 * A ^ 2 * δ := by ring
  have hne : (4 : ℂ) * A ^ 2 * δ ≠ 0 := by simp [hA, hδ]
  rw [hd, enorm_inv_rpow_of_ne_zero hne, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hA' : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hδ' : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_ofNat, neg_sub,
    Real.mul_rpow (by positivity) hδ'.le, Real.mul_rpow (by norm_num) (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul hA'.le]
  have : ‖A‖ ^ (t - 2) * ‖A‖ ^ (((2 : ℕ) : ℝ) * (1 - t)) = ‖A‖ ^ (-t) :=
    rpow_mul_rpow_eq hA' (by push_cast; ring)
  calc K * ‖A‖ ^ (t - 2) * (4 ^ (1 - t) * ‖A‖ ^ (((2 : ℕ) : ℝ) * (1 - t)) * ‖δ‖ ^ (1 - t))
      = K * 4 ^ (1 - t) * (‖A‖ ^ (t - 2) * ‖A‖ ^ (((2 : ℕ) : ℝ) * (1 - t))) * ‖δ‖ ^ (1 - t) := by
        ring
    _ = _ := by rw [this]

/-- The constant of the weighted quadratic bound `eq:quadw`. -/
noncomputable def quadW (K t γ : ℝ) : ℝ :=
  2 * K * 4 ^ (1 - t) +
    (4 / 3) ^ t * (2 * π) * (2 ^ (2 - 2 * t) / (2 * t - 2) + 2 ^ (2 - 2 * t + γ) / (2 * t - γ - 2))

/-- `quadW` is nonnegative in the range where it is used. -/
theorem quadW_nonneg {K t γ : ℝ} (hK0 : 0 ≤ K) (ht : 1 < t) (hγt : γ < 2 * t - 2) :
    0 ≤ quadW K t γ := by
  unfold quadW
  have h1 : 0 < 2 * t - 2 := by linarith
  have h2 : 0 < 2 * t - γ - 2 := by linarith
  positivity

/-- The pointwise split behind `eq:quadw`: near the double point `|z - c| ≤ 2ρ` (with
`ρ = |δ|^{1/2}`) the weight is bounded, and far from it the quadratic is comparable to
`|A| |z - c|²`. -/
private lemma weighted_pointwise {t γ : ℝ} (ht : 0 < t) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {A c δ : ℂ} (hA : A ≠ 0) (z : ℂ) :
    ENNReal.ofReal (‖z‖ ^ γ) * ‖A * ((z - c) ^ 2 - δ)‖ₑ⁻¹ ^ t ≤
      ENNReal.ofReal (‖c‖ ^ γ + (2 * √‖δ‖) ^ γ) * ‖A * ((z - c) ^ 2 - δ)‖ₑ⁻¹ ^ t +
        {z : ℂ | 2 * √‖δ‖ < ‖z - c‖}.indicator (fun z =>
          ENNReal.ofReal ((4 / 3) ^ t * ‖A‖ ^ (-t)) *
            (ENNReal.ofReal (‖c‖ ^ γ) * ‖z - c‖ₑ⁻¹ ^ (2 * t) + ‖z - c‖ₑ⁻¹ ^ (2 * t - γ))) z := by
  set ρ := √‖δ‖ with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ2 : ρ ^ 2 = ‖δ‖ := Real.sq_sqrt (norm_nonneg _)
  have hzc : ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by
    calc ‖z‖ = ‖c + (z - c)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  by_cases hN : z ∈ {z : ℂ | 2 * ρ < ‖z - c‖}
  · rw [indicator_of_mem hN]
    refine le_trans ?_ le_add_self
    have hr : 2 * ρ < ‖z - c‖ := hN
    set r := ‖z - c‖ with hr_def
    have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr
    have hzc0 : z - c ≠ 0 := norm_pos_iff.mp hr0
    have hA' : 0 < ‖A‖ := norm_pos_iff.mpr hA
    -- the lower bound on the quadratic
    have hq : 3 / 4 * ‖A‖ * r ^ 2 ≤ ‖A * ((z - c) ^ 2 - δ)‖ := by
      have h1 : ‖δ‖ ≤ r ^ 2 / 4 := by nlinarith
      have h2 : r ^ 2 - ‖δ‖ ≤ ‖(z - c) ^ 2 - δ‖ := by
        have := norm_sub_norm_le ((z - c) ^ 2) δ
        rwa [norm_pow] at this
      rw [norm_mul]
      nlinarith
    have hq0 : 0 < ‖A * ((z - c) ^ 2 - δ)‖ := lt_of_lt_of_le (by positivity) hq
    rw [enorm_inv_rpow_of_ne_zero (norm_pos_iff.mp hq0), enorm_inv_rpow_of_ne_zero hzc0,
      enorm_inv_rpow_of_ne_zero hzc0, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ‖z‖ ^ γ),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ‖c‖ ^ γ),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (4 / 3) ^ t * ‖A‖ ^ (-t))]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 : ‖A * ((z - c) ^ 2 - δ)‖ ^ (-t) ≤ (4 / 3) ^ t * ‖A‖ ^ (-t) * r ^ (-(2 * t)) := by
      calc ‖A * ((z - c) ^ 2 - δ)‖ ^ (-t) ≤ (3 / 4 * ‖A‖ * r ^ 2) ^ (-t) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hq (by linarith)
        _ = (4 / 3) ^ t * ‖A‖ ^ (-t) * r ^ (-(2 * t)) := by
            rw [Real.mul_rpow (by positivity) (by positivity),
              Real.mul_rpow (by norm_num) hA'.le, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le,
              Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3 / 4), ← Real.inv_rpow (by norm_num)]
            norm_num
    have e2 : ‖z‖ ^ γ ≤ ‖c‖ ^ γ + r ^ γ :=
      (Real.rpow_le_rpow (norm_nonneg _) hzc hγ0).trans
        (Real.rpow_add_le_add_rpow (norm_nonneg _) hr0.le hγ0 hγ1)
    have e3 : r ^ γ * r ^ (-(2 * t)) = r ^ (-(2 * t - γ)) := rpow_mul_rpow_eq hr0 (by ring)
    calc ‖z‖ ^ γ * ‖A * ((z - c) ^ 2 - δ)‖ ^ (-t)
        ≤ (‖c‖ ^ γ + r ^ γ) * ((4 / 3) ^ t * ‖A‖ ^ (-t) * r ^ (-(2 * t))) := by gcongr
      _ = (4 / 3) ^ t * ‖A‖ ^ (-t) * (‖c‖ ^ γ * r ^ (-(2 * t)) + r ^ γ * r ^ (-(2 * t))) := by
          ring
      _ = _ := by rw [e3]
  · rw [indicator_of_notMem hN, add_zero]
    have hr : ‖z - c‖ ≤ 2 * ρ := not_lt.mp hN
    gcongr
    exact (Real.rpow_le_rpow (norm_nonneg _) (hzc.trans (by linarith)) hγ0).trans
      (Real.rpow_add_le_add_rpow (norm_nonneg _) (by positivity) hγ0 hγ1)

/-- **The weighted full-plane quadratic bound `eq:quadw`**: for `1 < t`, `0 ≤ γ ≤ 1`,
`γ < 2t - 2` and `A, δ ≠ 0`,
`∫_ℂ |z|^γ |A((z - c)² - δ)|^{-t} ≤ M |A|^{-t} |δ|^{1-t} (|c|^γ + |δ|^{γ/2})`. -/
theorem lintegral_rpow_mul_inv_quadratic_le {t K γ : ℝ} (hK : FullPlaneQuadratic t K)
    (hK0 : 0 ≤ K) (ht : 1 < t) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hγt : γ < 2 * t - 2)
    {A c δ : ℂ} (hA : A ≠ 0) (hδ : δ ≠ 0) :
    ∫⁻ z, ENNReal.ofReal (‖z‖ ^ γ) * ‖A * ((z - c) ^ 2 - δ)‖ₑ⁻¹ ^ t ≤
      ENNReal.ofReal (quadW K t γ * ‖A‖ ^ (-t) * ‖δ‖ ^ (1 - t) * (‖c‖ ^ γ + ‖δ‖ ^ (γ / 2))) := by
  set ρ := √‖δ‖ with hρ
  have hδ' : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr hδ'
  have hA' : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hρpow : ∀ x : ℝ, ρ ^ x = ‖δ‖ ^ (x / 2) := fun x => by
    rw [hρ, Real.sqrt_eq_rpow, ← Real.rpow_mul hδ'.le]; ring_nf
  set N := {z : ℂ | 2 * ρ < ‖z - c‖} with hN
  have hNm : MeasurableSet N := measurableSet_lt measurable_const (by fun_prop)
  set k := (4 / 3 : ℝ) ^ t * ‖A‖ ^ (-t)
  -- the far part, after translating `w = z - c`
  have hfar : ∫⁻ z, N.indicator (fun z => ENNReal.ofReal k *
      (ENNReal.ofReal (‖c‖ ^ γ) * ‖z - c‖ₑ⁻¹ ^ (2 * t) + ‖z - c‖ₑ⁻¹ ^ (2 * t - γ))) z =
      ENNReal.ofReal k * (ENNReal.ofReal (‖c‖ ^ γ) *
        ENNReal.ofReal (2 * π * ((2 * ρ) ^ (2 - 2 * t) / (2 * t - 2))) +
        ENNReal.ofReal (2 * π * ((2 * ρ) ^ (2 - (2 * t - γ)) / (2 * t - γ - 2)))) := by
    have e : (fun z => N.indicator (fun z => ENNReal.ofReal k *
        (ENNReal.ofReal (‖c‖ ^ γ) * ‖z - c‖ₑ⁻¹ ^ (2 * t) + ‖z - c‖ₑ⁻¹ ^ (2 * t - γ))) z) =
        fun z => {w : ℂ | 2 * ρ < ‖w‖}.indicator (fun w => ENNReal.ofReal k *
          (ENNReal.ofReal (‖c‖ ^ γ) * ‖w‖ₑ⁻¹ ^ (2 * t) + ‖w‖ₑ⁻¹ ^ (2 * t - γ))) (z - c) := by
      funext z
      simp only [hN, indicator, mem_ofPred_eq]
    rw [e, lintegral_sub_right_eq_self (fun w => {w : ℂ | 2 * ρ < ‖w‖}.indicator (fun w =>
      ENNReal.ofReal k * (ENNReal.ofReal (‖c‖ ^ γ) * ‖w‖ₑ⁻¹ ^ (2 * t) + ‖w‖ₑ⁻¹ ^ (2 * t - γ))) w) c,
      lintegral_indicator (measurableSet_lt measurable_const measurable_norm),
      lintegral_const_mul _ (by fun_prop), lintegral_add_left (by fun_prop),
      lintegral_const_mul _ (by fun_prop),
      lintegral_norm_gt_inv_rpow (by linarith) (by positivity),
      lintegral_norm_gt_inv_rpow (by linarith) (by positivity)]
  have hm1 : Measurable fun z : ℂ =>
      ENNReal.ofReal (‖c‖ ^ γ + (2 * ρ) ^ γ) * ‖A * ((z - c) ^ 2 - δ)‖ₑ⁻¹ ^ t := by fun_prop
  calc ∫⁻ z, ENNReal.ofReal (‖z‖ ^ γ) * ‖A * ((z - c) ^ 2 - δ)‖ₑ⁻¹ ^ t
      ≤ ∫⁻ z, (ENNReal.ofReal (‖c‖ ^ γ + (2 * ρ) ^ γ) * ‖A * ((z - c) ^ 2 - δ)‖ₑ⁻¹ ^ t +
          N.indicator (fun z => ENNReal.ofReal k *
            (ENNReal.ofReal (‖c‖ ^ γ) * ‖z - c‖ₑ⁻¹ ^ (2 * t) + ‖z - c‖ₑ⁻¹ ^ (2 * t - γ))) z) :=
        lintegral_mono fun z => weighted_pointwise (by linarith) hγ0 hγ1 hA z
    _ = ENNReal.ofReal (‖c‖ ^ γ + (2 * ρ) ^ γ) * (∫⁻ z, ‖A * ((z - c) ^ 2 - δ)‖ₑ⁻¹ ^ t) +
          ENNReal.ofReal k * (ENNReal.ofReal (‖c‖ ^ γ) *
            ENNReal.ofReal (2 * π * ((2 * ρ) ^ (2 - 2 * t) / (2 * t - 2))) +
            ENNReal.ofReal (2 * π * ((2 * ρ) ^ (2 - (2 * t - γ)) / (2 * t - γ - 2)))) := by
        rw [lintegral_add_left hm1, lintegral_const_mul _ (by fun_prop), hfar]
    _ ≤ ENNReal.ofReal (‖c‖ ^ γ + (2 * ρ) ^ γ) *
          ENNReal.ofReal (K * 4 ^ (1 - t) * ‖A‖ ^ (-t) * ‖δ‖ ^ (1 - t)) +
          ENNReal.ofReal k * (ENNReal.ofReal (‖c‖ ^ γ) *
            ENNReal.ofReal (2 * π * ((2 * ρ) ^ (2 - 2 * t) / (2 * t - 2))) +
            ENNReal.ofReal (2 * π * ((2 * ρ) ^ (2 - (2 * t - γ)) / (2 * t - γ - 2)))) := by
        gcongr
        exact lintegral_inv_quadratic_le hK hK0 hA hδ
    _ ≤ _ := by
        have h1 : 0 < 2 * t - 2 := by linarith
        have h2 : 0 < 2 * t - γ - 2 := by linarith
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        -- substitute the powers of `ρ`
        have r1 : (2 * ρ) ^ γ = 2 ^ γ * ‖δ‖ ^ (γ / 2) := by
          rw [Real.mul_rpow (by norm_num) hρ0.le, hρpow]
        have r2 : (2 * ρ) ^ (2 - 2 * t) = 2 ^ (2 - 2 * t) * ‖δ‖ ^ (1 - t) := by
          rw [Real.mul_rpow (by norm_num) hρ0.le, hρpow]; ring_nf
        have r3 : (2 * ρ) ^ (2 - (2 * t - γ)) =
            2 ^ (2 - 2 * t + γ) * (‖δ‖ ^ (1 - t) * ‖δ‖ ^ (γ / 2)) := by
          rw [Real.mul_rpow (by norm_num) hρ0.le, hρpow,
            rpow_mul_rpow_eq hδ' (show 1 - t + γ / 2 = (2 - (2 * t - γ)) / 2 by ring)]
          ring_nf
        rw [r1, r2, r3]
        set a := ‖A‖ ^ (-t)
        set d := ‖δ‖ ^ (1 - t)
        set C := ‖c‖ ^ γ
        set E := ‖δ‖ ^ (γ / 2)
        set P := K * 4 ^ (1 - t)
        set U1 := (4 / 3 : ℝ) ^ t * (2 * π) * (2 ^ (2 - 2 * t) / (2 * t - 2))
        set U2 := (4 / 3 : ℝ) ^ t * (2 * π) * (2 ^ (2 - 2 * t + γ) / (2 * t - γ - 2))
        have ha : 0 ≤ a := by positivity
        have hd : 0 ≤ d := by positivity
        have hC : 0 ≤ C := by positivity
        have hE : 0 ≤ E := by positivity
        have hP : 0 ≤ P := by positivity
        have hU1 : 0 ≤ U1 := by positivity
        have hU2 : 0 ≤ U2 := by positivity
        have h2γ : (2 : ℝ) ^ γ ≤ 2 := by
          calc (2 : ℝ) ^ γ ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hγ1
            _ = 2 := Real.rpow_one 2
        have hW : quadW K t γ = 2 * P + U1 + U2 := by simp only [quadW, P, U1, U2]; ring
        have lhs : (C + 2 ^ γ * E) * (P * a * d) +
            (4 / 3) ^ t * a * (C * (2 * π * (2 ^ (2 - 2 * t) * d / (2 * t - 2))) +
              2 * π * (2 ^ (2 - 2 * t + γ) * (d * E) / (2 * t - γ - 2))) =
            a * d * (P * (C + 2 ^ γ * E) + U1 * C + U2 * E) := by
          simp only [U1, U2]; field_simp; ring
        have key : P * (C + 2 ^ γ * E) + U1 * C + U2 * E ≤ (2 * P + U1 + U2) * (C + E) := by
          nlinarith [mul_nonneg hP hC, mul_nonneg hP hE, mul_nonneg hU1 hE, mul_nonneg hU2 hC,
            mul_le_mul_of_nonneg_left h2γ (mul_nonneg hP hE)]
        calc (C + 2 ^ γ * E) * (K * 4 ^ (1 - t) * a * d) +
            (4 / 3) ^ t * a * (C * (2 * π * (2 ^ (2 - 2 * t) * d / (2 * t - 2))) +
              2 * π * (2 ^ (2 - 2 * t + γ) * (d * E) / (2 * t - γ - 2)))
            = a * d * (P * (C + 2 ^ γ * E) + U1 * C + U2 * E) := by rw [← lhs]
          _ ≤ a * d * ((2 * P + U1 + U2) * (C + E)) := by gcongr
          _ = quadW K t γ * a * d * (C + E) := by rw [hW]; ring

end SLT.MiddlePositions.Two
