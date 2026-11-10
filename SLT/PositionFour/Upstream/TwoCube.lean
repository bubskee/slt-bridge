/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Upstream.RefFibre
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# The two-cube pushforward (note §1.1, step 3)

`twoCubeBound`: the pushforward of Lebesgue measure under `Ψ(l, m) = l³ + m³` is at most
`(2/9) |𝔇|^{-4/3}` times Lebesgue measure on cubic space (moment coordinates):

`TwoCubeBound (2/9) : volume.map twoCube ≤ ofReal (2/9) • volume.withDensity twoCubeDensity`.

Ingredients, as in the note:
* the complex Jacobian `det_ℂ DΨ = 9 det(l, m)⁴` in moment coordinates (`det_twoCubeJac`);
  the real Jacobian is its squared modulus, `81 |det(l, m)|⁸ = 81 |𝔇(Ψ)|^{4/3}`;
* the fibre bound `18` (Sylvester's uniqueness, `exists_finset_twoCube_fibre`);
* the change of variables with bounded multiplicity (`lintegral_abs_det_fderiv_mul_le`);
* the critical set `{det = 0}` is Lebesgue-null (`volume_det2_eq_zero`).

The bound `≤` is all that is proved; equality (which also needs Sylvester's existence and the
nullity of `{𝔇 = 0}`) is not needed downstream.
-/

@[expose] public section

namespace SLT.PositionFour

open MeasureTheory Set
open scoped ENNReal

/-- **Step 3 as a statement.** The pushforward of Lebesgue measure under the two-cube map is at
most `K |𝔇|^{-4/3}` times Lebesgue measure. -/
def TwoCubeBound (K : ℝ) : Prop :=
  (volume : Measure (Form × Form)).map twoCube ≤
    ENNReal.ofReal K • (volume : Measure Cubic).withDensity twoCubeDensity

/-- The two-cube map in the coordinates `x = (a, b, c, d)` of `Cubic`. -/
def twoCubeC (x : Cubic) : Cubic :=
  ![x 0 ^ 3 + x 2 ^ 3, x 0 ^ 2 * x 1 + x 2 ^ 2 * x 3, x 0 * x 1 ^ 2 + x 2 * x 3 ^ 2,
    x 1 ^ 3 + x 3 ^ 3]

/-- `twoCubeC` is the two-cube map composed with `cubicEquiv`. -/
theorem twoCubeC_eq (x : Cubic) : twoCubeC x = twoCube (cubicEquiv x) := by
  ext i; fin_cases i <;> simp [twoCubeC, twoCube, cube]

/-- The complex Jacobian matrix of `twoCubeC` (rows: moment coordinates; columns: `a, b, c, d`). -/
def twoCubeJac (x : Cubic) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![3 * x 0 ^ 2, 0, 3 * x 2 ^ 2, 0;
     2 * x 0 * x 1, x 0 ^ 2, 2 * x 2 * x 3, x 2 ^ 2;
     x 1 ^ 2, 2 * x 0 * x 1, x 3 ^ 2, 2 * x 2 * x 3;
     0, 3 * x 1 ^ 2, 0, 3 * x 3 ^ 2]

/-- `det_ℂ DΨ = 9 det(l, m)⁴` in moment coordinates. -/
theorem det_twoCubeJac (x : Cubic) :
    (twoCubeJac x).det = 9 * (x 0 * x 3 - x 1 * x 2) ^ 4 := by
  rw [Matrix.det_succ_row_zero]
  simp [twoCubeJac, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix,
    Fin.succAbove]
  ring

/-- The derivative of `twoCubeC`, as a continuous complex-linear map. -/
noncomputable def twoCubeDeriv (x : Cubic) : Cubic →L[ℂ] Cubic :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (twoCubeJac x))

/-- `twoCubeC` has complex derivative `twoCubeDeriv`. -/
theorem hasFDerivAt_twoCubeC (x : Cubic) : HasFDerivAt twoCubeC (twoCubeDeriv x) x := by
  refine hasFDerivAt_pi'.mpr fun i => ?_
  have h0 := hasFDerivAt_apply (𝕜 := ℂ) (F' := fun _ : Fin 4 => ℂ) 0 x
  have h1 := hasFDerivAt_apply (𝕜 := ℂ) (F' := fun _ : Fin 4 => ℂ) 1 x
  have h2 := hasFDerivAt_apply (𝕜 := ℂ) (F' := fun _ : Fin 4 => ℂ) 2 x
  have h3 := hasFDerivAt_apply (𝕜 := ℂ) (F' := fun _ : Fin 4 => ℂ) 3 x
  fin_cases i
  · refine ((h0.pow 3).add (h2.pow 3)).congr_fderiv ?_
    ext v
    simp [twoCubeDeriv, twoCubeJac, Matrix.toLin'_apply, dotProduct,
      Fin.sum_univ_four]
  · refine (((h0.pow 2).mul h1).add ((h2.pow 2).mul h3)).congr_fderiv ?_
    ext v
    simp [twoCubeDeriv, twoCubeJac, Matrix.toLin'_apply, dotProduct,
      Fin.sum_univ_four]
    ring
  · refine ((h0.mul (h1.pow 2)).add (h2.mul (h3.pow 2))).congr_fderiv ?_
    ext v
    simp [twoCubeDeriv, twoCubeJac, Matrix.toLin'_apply, dotProduct,
      Fin.sum_univ_four]
    ring
  · refine ((h1.pow 3).add (h3.pow 3)).congr_fderiv ?_
    ext v
    simp [twoCubeDeriv, twoCubeJac, Matrix.toLin'_apply, dotProduct,
      Fin.sum_univ_four]

/-- The real Jacobian of the two-cube map: `|det_ℂ|² = |9 det(l, m)⁴|²`. -/
theorem det_twoCubeDeriv (x : Cubic) :
    ((twoCubeDeriv x).restrictScalars ℝ).det =
      Complex.normSq (9 * (x 0 * x 3 - x 1 * x 2) ^ 4) := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, twoCubeDeriv,
    LinearMap.coe_toContinuousLinearMap, det_restrictScalars_complex, LinearMap.det_toLin',
    det_twoCubeJac]

/-- `det(l, m)` in the coordinates of `Cubic`. -/
theorem det2_cubicEquiv (x : Cubic) : det2 (cubicEquiv x) = x 0 * x 3 - x 1 * x 2 := rfl

/-- **The two-cube bound, integral form.** For measurable `φ ≥ 0`,
`∫ φ(l³ + m³) dl dm ≤ (2/9) ∫ φ(P) |𝔇(P)|^{-4/3} dP`. -/
theorem lintegral_twoCube_le {φ : Cubic → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ g : Form × Form, φ (twoCube g) ≤
      ENNReal.ofReal (2 / 9) * ∫⁻ P, φ P * twoCubeDensity P := by
  set s : Set Cubic := {x | det2 (cubicEquiv x) ≠ 0}
  have hs : MeasurableSet s :=
    (measurableSet_eq_fun (by simp only [det2_cubicEquiv]; fun_prop) measurable_const).compl
  set f' : Cubic → Cubic →L[ℝ] Cubic := fun x => (twoCubeDeriv x).restrictScalars ℝ
  have hf' : ∀ x ∈ s, HasFDerivWithinAt twoCubeC (f' x) s x := fun x _ =>
    ((hasFDerivAt_twoCubeC x).restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ x ∈ s, (f' x).det ≠ 0 := fun x hx => by
    simp only [f', det_twoCubeDeriv]
    refine (Complex.normSq_pos.mpr (mul_ne_zero (by norm_num) (pow_ne_zero 4 ?_))).ne'
    rwa [← det2_cubicEquiv]
  have hN : ∀ y : Cubic, ∃ F : Finset Cubic, F.card ≤ 18 ∧
      ∀ x ∈ s, twoCubeC x = y → x ∈ F := by
    intro y
    obtain ⟨F₀, hF₀, hmem⟩ := exists_finset_twoCube_fibre y
    classical
    refine ⟨F₀.image cubicEquiv.symm, Finset.card_image_le.trans hF₀, fun x hx hxy => ?_⟩
    refine Finset.mem_image.mpr ⟨cubicEquiv x, hmem _ hx ?_, cubicEquiv.symm_apply_apply x⟩
    rw [← twoCubeC_eq, hxy]
  set ψ : Cubic → ℝ≥0∞ := fun P => (ENNReal.ofReal 81)⁻¹ * (φ P * twoCubeDensity P)
  have hψ : Measurable ψ := by fun_prop
  have key := lintegral_abs_det_fderiv_mul_le volume hs hf' hdet hN hψ
  have hpt : ∀ x ∈ s, ENNReal.ofReal |(f' x).det| * ψ (twoCubeC x) = φ (twoCubeC x) := by
    intro x hx
    have hD : x 0 * x 3 - x 1 * x 2 ≠ 0 := hx
    have hDe : ‖x 0 * x 3 - x 1 * x 2‖ₑ ≠ 0 := enorm_ne_zero.mpr hD
    have hdens : twoCubeDensity (twoCubeC x) = ‖x 0 * x 3 - x 1 * x 2‖ₑ ^ (-(8 : ℝ)) := by
      rw [twoCubeDensity, twoCubeC_eq, disc_twoCube, det2_cubicEquiv, inv_nnnorm_rpow,
        enorm_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    have hreal : Complex.normSq (9 * (x 0 * x 3 - x 1 * x 2) ^ 4) =
        81 * ‖x 0 * x 3 - x 1 * x 2‖ ^ 8 := by
      rw [Complex.normSq_eq_norm_sq, norm_mul, norm_pow]; norm_num; ring
    have habs : ENNReal.ofReal |(f' x).det| =
        ENNReal.ofReal 81 * ‖x 0 * x 3 - x 1 * x 2‖ₑ ^ (8 : ℝ) := by
      simp only [f', det_twoCubeDeriv]
      rw [abs_of_nonneg (Complex.normSq_nonneg _), hreal, ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ← ENNReal.rpow_natCast]
      norm_num
    set D := x 0 * x 3 - x 1 * x 2
    rw [habs]
    simp only [ψ]
    rw [hdens]
    have h81 : ENNReal.ofReal 81 * (ENNReal.ofReal 81)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel (by norm_num) ENNReal.ofReal_ne_top
    have h8 : ‖D‖ₑ ^ (8 : ℝ) * ‖D‖ₑ ^ (-(8 : ℝ)) = 1 := by
      rw [← ENNReal.rpow_add _ _ hDe enorm_ne_top]; simp
    calc ENNReal.ofReal 81 * ‖D‖ₑ ^ (8 : ℝ) *
          ((ENNReal.ofReal 81)⁻¹ * (φ (twoCubeC x) * ‖D‖ₑ ^ (-(8 : ℝ))))
        = (ENNReal.ofReal 81 * (ENNReal.ofReal 81)⁻¹) * φ (twoCubeC x) *
            (‖D‖ₑ ^ (8 : ℝ) * ‖D‖ₑ ^ (-(8 : ℝ))) := by ring
      _ = φ (twoCubeC x) := by rw [h81, h8, one_mul, mul_one]
  have hnull : volume {x : Cubic | det2 (cubicEquiv x) = 0} = 0 := by
    have := measurePreserving_cubicEquiv.measure_preimage
      (s := {g : Form × Form | det2 g = 0})
      (measurableSet_eq_fun (by unfold det2; fun_prop) measurable_const).nullMeasurableSet
    rw [← volume_det2_eq_zero, ← this]; rfl
  have hae : ∀ᵐ x ∂(volume : Measure Cubic), x ∈ s := by
    refine ae_iff.mpr ?_
    simpa [s] using hnull
  calc ∫⁻ g : Form × Form, φ (twoCube g) = ∫⁻ x : Cubic, φ (twoCube (cubicEquiv x)) :=
        (measurePreserving_cubicEquiv.lintegral_comp_emb cubicEquiv.measurableEmbedding _).symm
    _ = ∫⁻ x in s, φ (twoCubeC x) := by
        rw [Measure.restrict_eq_self_of_ae_mem hae]; simp_rw [twoCubeC_eq]
    _ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * ψ (twoCubeC x) :=
        (setLIntegral_congr_fun hs hpt).symm
    _ ≤ ((18 : ℕ) : ℝ≥0∞) * ∫⁻ P, ψ P := key
    _ = ENNReal.ofReal (2 / 9) * ∫⁻ P, φ P * twoCubeDensity P := by
        rw [lintegral_const_mul _ (by fun_prop), ← mul_assoc]
        congr 1
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (by norm_num),
          ← ENNReal.ofReal_mul (by norm_num)]
        norm_num

/-- **The two-cube bound (step 3), proved.** -/
theorem twoCubeBound : TwoCubeBound (2 / 9) := by
  refine Measure.le_iff.mpr fun A hA => ?_
  have hm : Measurable twoCube := by unfold twoCube cube; fun_prop
  rw [Measure.map_apply hm hA, Measure.smul_apply, withDensity_apply _ hA, smul_eq_mul]
  have h := lintegral_twoCube_le (φ := A.indicator 1) (measurable_one.indicator hA)
  have e1 : ∫⁻ g : Form × Form, A.indicator 1 (twoCube g) = volume (twoCube ⁻¹' A) := by
    rw [← lintegral_indicator_one (hm hA)]; rfl
  have e2 : ∫⁻ P, A.indicator 1 P * twoCubeDensity P = ∫⁻ P in A, twoCubeDensity P := by
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun P => ?_
    by_cases hP : P ∈ A <;> simp [hP]
  rw [e1, e2] at h
  exact h

end SLT.PositionFour
