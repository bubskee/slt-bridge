/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Complex-linear changes of variables

* `det_restrictScalars_complex`: the real determinant of a complex-linear map is `|det_ℂ|²`;
* `lintegral_comp_complexLinear`: a complex-linear substitution `x = L u` rescales Lebesgue
  measure by `|det_ℂ L|²`;
* `lintegral_comp_mul_left`: the case of complex scaling on `ℂ`, `|d|²`.
-/

@[expose] public section

namespace SLT.Pushforward

open MeasureTheory Set
open scoped ENNReal

/-! ### Real determinants of complex-linear maps -/

/-- The real determinant of a complex-linear map is the squared modulus of its complex
determinant. -/
theorem det_restrictScalars_complex {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : V →ₗ[ℂ] V) :
    (L.restrictScalars ℝ).det = Complex.normSq L.det := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

/-- A complex-linear substitution rescales Lebesgue measure by `|det_ℂ L|²`:
`∫ F(L u) du = |det L|⁻² ∫ F`. -/
theorem lintegral_comp_complexLinear {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (L : V →ₗ[ℂ] V) (hL : L.det ≠ 0) {F : V → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ u, F (L u) ∂μ = (ENNReal.ofReal (Complex.normSq L.det))⁻¹ * ∫⁻ x, F x ∂μ := by
  have hdet : (L.restrictScalars ℝ).det ≠ 0 := by
    rw [det_restrictScalars_complex]; exact (Complex.normSq_pos.mpr hL).ne'
  have hmeas : Measurable (L.restrictScalars ℝ) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet
  rw [det_restrictScalars_complex] at hmap
  calc ∫⁻ u, F (L u) ∂μ = ∫⁻ u, F ((L.restrictScalars ℝ) u) ∂μ := rfl
    _ = ∫⁻ x, F x ∂(Measure.map (L.restrictScalars ℝ) μ) := (lintegral_map hF hmeas).symm
    _ = _ := by
        rw [hmap, lintegral_smul_measure, abs_inv, abs_of_nonneg (Complex.normSq_nonneg _),
          ENNReal.ofReal_inv_of_pos (Complex.normSq_pos.mpr hL)]
        rfl

/-- **Complex scaling.** `∫ F(d z) dz = |d|⁻² ∫ F` on `ℂ`. -/
theorem lintegral_comp_mul_left {d : ℂ} (hd : d ≠ 0) {F : ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F (d * z) = (ENNReal.ofReal (Complex.normSq d))⁻¹ * ∫⁻ z, F z := by
  have hdet : (d • LinearMap.id : ℂ →ₗ[ℂ] ℂ).det = d := by
    rw [LinearMap.det_smul, LinearMap.det_id, Module.finrank_self, pow_one, mul_one]
  have := lintegral_comp_complexLinear volume (d • LinearMap.id : ℂ →ₗ[ℂ] ℂ)
    (by rwa [hdet]) hF
  rw [hdet] at this
  simpa using this

end SLT.Pushforward
