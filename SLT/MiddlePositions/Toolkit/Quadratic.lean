/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Defs
public import SLT.Pushforward.Quadratic

/-!
# The full-plane quadratic interface (note §2, Lemma "Planar powers and quadratics")

* `fullPlaneQuadratic`: the interface statement `FullPlaneQuadratic t C` for every `1 < t < 2`,
  with the explicit constant `quadC t = 4^{t-1} (K_t + 1)`, read off the exact full-plane
  integral `SLT.Pushforward.lintegral_quadratic_eq_rpow`.
-/

@[expose] public section

namespace SLT.MiddlePositions

open MeasureTheory Set Metric SLT.PositionFour SLT.Pushforward
open scoped ENNReal

/-- The constant of `fullPlaneQuadratic`: `4^{t-1} (K_t + 1)`. -/
noncomputable def quadC (t : ℝ) : ℝ := 4 ^ (t - 1) * ((quadConstT t).toReal + 1)

/-- `quadC t > 0`. -/
theorem quadC_pos (t : ℝ) : 0 < quadC t := by
  unfold quadC; positivity

/-- `‖z‖ₑ⁻¹ ^ a = ofReal (‖z‖ ^ (-a))` away from `0`. -/
theorem enorm_inv_rpow_eq_ofReal {z : ℂ} (hz : z ≠ 0) (a : ℝ) :
    ‖z‖ₑ⁻¹ ^ a = ENNReal.ofReal (‖z‖ ^ (-a)) := by
  rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg, enorm_rpow_eq_ofReal hz]

/-- **Interface 3, proved.** For `1 < t < 2` and `A ≠ 0`,
`∫_ℂ |A z² + B z + D|^{-t} ≤ C |A|^{t-2} |B² - 4AD|^{1-t}` with `C = quadC t`. -/
theorem fullPlaneQuadratic_quadC {t : ℝ} (ht1 : 1 < t) (ht2 : t < 2) :
    FullPlaneQuadratic t (quadC t) := by
  intro A B D hA
  have ha : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hCA : 0 < quadC t * ‖A‖ ^ (t - 2) := mul_pos (quadC_pos t) (by positivity)
  by_cases hΔ : B ^ 2 - 4 * A * D = 0
  · rw [hΔ, enorm_zero, ENNReal.inv_zero, ENNReal.top_rpow_of_pos (by linarith),
      ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hCA)]
    exact le_top
  have hK := quadConstT_lt_top ht1 ht2
  have hδ : 0 < ‖B ^ 2 - 4 * A * D‖ := norm_pos_iff.mpr hΔ
  have hlhs : ∫⁻ z : ℂ, ‖A * z ^ 2 + B * z + D‖ₑ⁻¹ ^ t =
      ∫⁻ z : ℂ, ‖A * z ^ 2 + B * z + D‖ₑ ^ (-t) :=
    lintegral_congr fun z => by rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]
  rw [hlhs, lintegral_quadratic_eq_rpow hA hΔ t, enorm_inv_rpow_eq_ofReal hΔ,
    ← ENNReal.ofReal_toReal hK.ne, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul hCA.le]
  refine ENNReal.ofReal_le_ofReal ?_
  have hK0 : 0 ≤ (quadConstT t).toReal := ENNReal.toReal_nonneg
  have e : -(t - 1) = 1 - t := by ring
  rw [e, quadC]
  have h1 : 0 ≤ 4 ^ (t - 1) * ‖A‖ ^ (t - 2) * ‖B ^ 2 - 4 * A * D‖ ^ (1 - t) := by positivity
  nlinarith

/-- **Interface 3, proved (existential form).** `∀ t ∈ (1, 2), ∃ C, FullPlaneQuadratic t C`. -/
theorem fullPlaneQuadratic : ∀ t : ℝ, 1 < t → t < 2 → ∃ C, FullPlaneQuadratic t C :=
  fun _ ht1 ht2 => ⟨_, fullPlaneQuadratic_quadC ht1 ht2⟩

end SLT.MiddlePositions
