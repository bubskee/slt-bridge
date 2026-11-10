/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Inverse powers in `ℝ≥0∞`

The complex-margin files write inverse powers as `‖x‖ₑ⁻¹ ^ t` in `ℝ≥0∞`, which is `∞` at `x = 0`
for `t > 0`. These lemmas convert them to real powers away from `0` and split products and powers.
They are shared by `SLT/PositionFour` and `SLT/MiddlePositions`.
-/

@[expose] public section

namespace SLT.Pushforward

open scoped ENNReal NNReal

/-- For `x ≠ 0`, `|x|^{-t}` in `ℝ≥0∞` is the real power. -/
theorem enorm_inv_rpow_of_ne_zero {x : ℂ} (hx : x ≠ 0) (t : ℝ) :
    ‖x‖ₑ⁻¹ ^ t = ENNReal.ofReal (‖x‖ ^ (-t)) := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [← ofReal_norm, ← ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_rpow_of_pos
    (inv_pos.mpr hpos), Real.inv_rpow hpos.le, Real.rpow_neg hpos.le]

/-- For `r > 0`, `r^{-t}` in `ℝ≥0∞` is the real power. -/
theorem ofReal_inv_rpow_of_pos {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (ENNReal.ofReal r)⁻¹ ^ t = ENNReal.ofReal (r ^ (-t)) := by
  rw [← ENNReal.ofReal_inv_of_pos hr, ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hr),
    Real.inv_rpow hr.le, Real.rpow_neg hr.le]

/-- `ofReal (x^{-a}) ≤ x^{-a}` in `ℝ≥0∞` (the real power is `0` at `x = 0`). -/
theorem ofReal_rpow_neg_le {x : ℝ} (hx : 0 ≤ x) (a : ℝ) :
    ENNReal.ofReal (x ^ (-a)) ≤ (ENNReal.ofReal x)⁻¹ ^ a := by
  rcases hx.eq_or_lt with rfl | hx
  · rcases lt_trichotomy a 0 with ha | rfl | ha
    · rw [Real.zero_rpow (by linarith), ENNReal.ofReal_zero]; exact bot_le
    · simp
    · rw [Real.zero_rpow (by linarith), ENNReal.ofReal_zero]; exact bot_le
  · rw [ofReal_inv_rpow_of_pos hx]

/-- The inverse power of a product, `|a x|^{-t} = |a|^{-t} |x|^{-t}`, for `a ≠ 0` and `t ≥ 0`. -/
theorem enorm_mul_inv_rpow {a : ℂ} (ha : a ≠ 0) (x : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖a * x‖ₑ⁻¹ ^ t = ENNReal.ofReal (‖a‖ ^ (-t)) * ‖x‖ₑ⁻¹ ^ t := by
  rw [enorm_mul, ENNReal.mul_inv (Or.inr enorm_ne_top) (Or.inl enorm_ne_top),
    ENNReal.mul_rpow_of_nonneg _ _ ht, enorm_inv_rpow_of_ne_zero ha]

/-- The inverse power of a power, `|x^n|^{-t} = |x|^{-n t}`. -/
theorem enorm_pow_inv_rpow (x : ℂ) (n : ℕ) (t : ℝ) :
    ‖x ^ n‖ₑ⁻¹ ^ t = ‖x‖ₑ⁻¹ ^ ((n : ℝ) * t) := by
  rw [enorm_pow, ENNReal.inv_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]

/-- A positive weight cancels part of an inverse power: `|x|^u |x|^{-(u+v)} ≤ |x|^{-v}` for
`u ≥ 0` (both sides are `∞`, or the left side is `0`, at `x = 0`). -/
theorem ofReal_rpow_mul_inv_rpow_le (x : ℂ) {u v : ℝ} (hu : 0 ≤ u) :
    ENNReal.ofReal (‖x‖ ^ u) * ‖x‖ₑ⁻¹ ^ (u + v) ≤ ‖x‖ₑ⁻¹ ^ v := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases hu.lt_or_eq with hu | rfl
    · simp [Real.zero_rpow hu.ne']
    · simp
  · rw [enorm_inv_rpow_of_ne_zero hx, enorm_inv_rpow_of_ne_zero hx,
      ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (norm_pos_iff.mpr hx)]
    exact le_of_eq (by ring_nf)

end SLT.Pushforward
