/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Upstream.Area
public import SLT.PositionFour.Upstream.Coords
public import SLT.PositionFour.Upstream.Reference
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Algebra.Polynomial.Roots
public import SLT.PositionFour.Upstream.Sylvester

/-!
# The weighted reference fibre (note §1.2, first paragraph)

The weighted fibre integral over `P* = s³ + t³`,
`refFibre β = ∫_{ℂ²} ‖u‖^β |𝔇(P* - u³)|^{-4/3} du`, is finite for `0 ≤ β < 2`
(`refFibre_lt_top`). This is the note's `ρ_β(P*) < ∞`, up to the two-cube constant. The proof
follows the note:

1. `𝔇(P* - u³) = Q(u₁³, u₂³)` with `Q(U, V) = (1 - U - V)² - 4 U V` (`disc_refCubic_sub_cube`);
2. the substitution `U = u³` in each variable (`lintegral_comp_cube_le`, degree `3`, Jacobian
   `|3u²|²`), giving the density `|U|^{-4/3} / 3`;
3. the substitution `U = x y`, `V = (1 - x)(1 - y)` (`lintegral_le_lintegral_rootMap`, degree `2`,
   Jacobian `|x - y|²`), with `Q = (x - y)²`;
4. the weight bound `max(|U|, |V|)^{β/3} ≤ (1 + |x|)^{β/3} (1 + |y|)^{β/3}`, which leaves
   the reference integral `∬ w_β(x) w_β(y) |x - y|^{-2/3}` of `Reference.lean`.
-/

@[expose] public section

namespace SLT.PositionFour

open MeasureTheory Set SLT.Pushforward
open scoped ENNReal

/-! ### The cube substitution on `ℂ` -/

/-- The real determinant of multiplication by `c` on `ℂ` is `|c|²`. -/
theorem det_smulRight_one (c : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det =
      Complex.normSq c := by
  have h : ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c : ℂ →L[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ) =
      c • LinearMap.id := by
    ext; simp [mul_comm]
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, h,
    det_restrictScalars_complex, LinearMap.det_smul, LinearMap.det_id, Module.finrank_self,
    pow_one, mul_one]

/-- **The cube substitution.** `∫_ℂ φ(z³) dz ≤ (1/3) ∫_ℂ φ(w) |w|^{-4/3} dw`. -/
theorem lintegral_comp_cube_le {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ z, φ (z ^ 3) ≤ 3⁻¹ * ∫⁻ w, φ w * ‖w‖ₑ ^ (-(4 / 3 : ℝ)) := by
  set s : Set ℂ := {z | z ≠ 0}
  have hs : MeasurableSet s := (measurableSet_singleton 0).compl
  set f' : ℂ → ℂ →L[ℝ] ℂ := fun z =>
    (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ((3 : ℕ) * z ^ (3 - 1))).restrictScalars ℝ
  have hf' : ∀ z ∈ s, HasFDerivWithinAt (fun z : ℂ => z ^ 3) (f' z) s z := fun z _ =>
    ((hasDerivAt_pow 3 z).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdetf : ∀ z, (f' z).det = 9 * ‖z‖ ^ 4 := fun z => by
    simp only [f', det_smulRight_one, Complex.normSq_eq_norm_sq, norm_mul, norm_pow]
    norm_num; ring
  have hdet : ∀ z ∈ s, (f' z).det ≠ 0 := fun z hz => by
    rw [hdetf]; have : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz; positivity
  have hN : ∀ y : ℂ, ∃ F : Finset ℂ, F.card ≤ 3 ∧ ∀ z ∈ s, z ^ 3 = y → z ∈ F := fun y =>
    ⟨Polynomial.nthRootsFinset 3 y,
      (Multiset.toFinset_card_le _).trans (by convert Polynomial.card_nthRoots 3 y),
      fun z _ hz => (Polynomial.mem_nthRootsFinset (by norm_num) y).mpr hz⟩
  set ψ : ℂ → ℝ≥0∞ := fun w => 9⁻¹ * (φ w * ‖w‖ₑ ^ (-(4 / 3 : ℝ)))
  have hψ : Measurable ψ := by fun_prop
  have key := lintegral_abs_det_fderiv_mul_le volume hs hf' hdet hN hψ
  have hpt : ∀ z ∈ s, ENNReal.ofReal |(f' z).det| * ψ (z ^ 3) = φ (z ^ 3) := by
    intro z hz
    have hz0 : ‖z‖ₑ ≠ 0 := enorm_ne_zero.mpr hz
    rw [hdetf, abs_of_nonneg (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    simp only [ψ, enorm_pow]
    have e1 : ‖z‖ₑ ^ 4 * (‖z‖ₑ ^ 3) ^ (-(4 / 3 : ℝ)) = 1 := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_add _ _ hz0 enorm_ne_top]
      norm_num
    have h9 : ENNReal.ofReal 9 * 9⁻¹ = 1 := by
      rw [show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
      exact ENNReal.mul_inv_cancel (by norm_num) (by simp)
    calc ENNReal.ofReal 9 * ‖z‖ₑ ^ 4 * (9⁻¹ * (φ (z ^ 3) * (‖z‖ₑ ^ 3) ^ (-(4 / 3 : ℝ))))
        = (ENNReal.ofReal 9 * 9⁻¹) * φ (z ^ 3) * (‖z‖ₑ ^ 4 * (‖z‖ₑ ^ 3) ^ (-(4 / 3 : ℝ))) := by
          ring
      _ = φ (z ^ 3) := by rw [h9, e1, one_mul, mul_one]
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ s := Measure.ae_ne volume 0
  calc ∫⁻ z, φ (z ^ 3) = ∫⁻ z in s, φ (z ^ 3) := by
        rw [Measure.restrict_eq_self_of_ae_mem hae]
    _ = ∫⁻ z in s, ENNReal.ofReal |(f' z).det| * ψ (z ^ 3) :=
        (setLIntegral_congr_fun hs hpt).symm
    _ ≤ ((3 : ℕ) : ℝ≥0∞) * ∫⁻ w, ψ w := key
    _ = 3⁻¹ * ∫⁻ w, φ w * ‖w‖ₑ ^ (-(4 / 3 : ℝ)) := by
        rw [lintegral_const_mul _ (by fun_prop), ← mul_assoc]
        congr 1
        rw [show (9 : ℝ≥0∞) = 3 * 3 by norm_num, ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
          Nat.cast_ofNat, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]

/-! ### The root substitution on `ℂ²` -/

/-- The reference discriminant `Q(U, V) = (1 - U - V)² - 4 U V`. -/
def refQ (p : ℂ × ℂ) : ℂ := (1 - p.1 - p.2) ^ 2 - 4 * p.1 * p.2

/-- The root map `(x, y) ↦ (x y, (1 - x)(1 - y))`. -/
def rootMap (q : ℂ × ℂ) : ℂ × ℂ := (q.1 * q.2, (1 - q.1) * (1 - q.2))

/-- `Q(x y, (1 - x)(1 - y)) = (x - y)²`. -/
theorem refQ_rootMap (q : ℂ × ℂ) : refQ (rootMap q) = (q.1 - q.2) ^ 2 := by
  simp only [refQ, rootMap]; ring

/-- The complex derivative of the root map. -/
theorem hasFDerivAt_rootMap (q : ℂ × ℂ) :
    HasFDerivAt (𝕜 := ℂ) rootMap
      (LinearMap.toContinuousLinearMap (lin2 q.2 q.1 (-(1 - q.2)) (-(1 - q.1)))) q := by
  have h1 : HasFDerivAt (𝕜 := ℂ) (fun q : ℂ × ℂ => q.1) (ContinuousLinearMap.fst ℂ ℂ ℂ) q :=
    hasFDerivAt_fst
  have h2 : HasFDerivAt (𝕜 := ℂ) (fun q : ℂ × ℂ => q.2) (ContinuousLinearMap.snd ℂ ℂ ℂ) q :=
    hasFDerivAt_snd
  have h := (h1.mul h2).prodMk (((hasFDerivAt_const (1 : ℂ) q).sub h1).mul
    ((hasFDerivAt_const (1 : ℂ) q).sub h2))
  refine h.congr_fderiv ?_
  ext <;> simp [lin2_apply]

/-- The real Jacobian of the root map is `|x - y|²`. -/
theorem det_rootMap (q : ℂ × ℂ) :
    ((LinearMap.toContinuousLinearMap (lin2 q.2 q.1 (-(1 - q.2)) (-(1 - q.1)))).restrictScalars
      ℝ).det = Complex.normSq (q.1 - q.2) := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.coe_toContinuousLinearMap, det_restrictScalars_complex, det_lin2]
  congr 1; ring

/-- Every `(U, V)` with `Q(U, V) ≠ 0` is `rootMap (x, y)` for some `x ≠ y`. -/
theorem mem_image_rootMap {p : ℂ × ℂ} (hp : refQ p ≠ 0) :
    p ∈ rootMap '' {q | q.1 ≠ q.2} := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (refQ p) two_pos
  have hδ0 : δ ≠ 0 := by rintro rfl; apply hp; rw [← hδ]; ring
  set S := 1 + p.1 - p.2
  refine ⟨((S + δ) / 2, (S - δ) / 2), ?_, ?_⟩
  · intro h
    apply hδ0
    linear_combination h
  · simp only [refQ] at hδ
    ext
    · simp only [rootMap, S]; linear_combination (-1 / 4 : ℂ) * hδ
    · simp only [rootMap, S]; linear_combination (-1 / 4 : ℂ) * hδ

/-- The zero set of `Q` is Lebesgue-null in `ℂ²`. -/
theorem volume_refQ_eq_zero : volume {p : ℂ × ℂ | refQ p = 0} = 0 := by
  have hS : MeasurableSet {p : ℂ × ℂ | refQ p = 0} :=
    measurableSet_eq_fun (by unfold refQ; fun_prop) measurable_const
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hS]
  refine Filter.Eventually.of_forall fun U => ?_
  obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_pow_nat_eq (4 * U) two_pos
  change volume (Prod.mk U ⁻¹' {p : ℂ × ℂ | refQ p = 0}) = 0
  refine measure_mono_null ?_
    (((Set.finite_singleton (1 + U + σ)).insert (1 + U - σ)).measure_zero (volume : Measure ℂ))
  intro V hV
  simp only [mem_preimage, mem_ofPred_eq, refQ] at hV
  have : (V - (1 + U)) ^ 2 = σ ^ 2 := by rw [hσ]; linear_combination hV
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with h | h
  · right; simp only [mem_singleton_iff]; linear_combination h
  · left; linear_combination h

/-- **The root substitution.** For measurable `H ≥ 0` on `ℂ²`,
`∫ H(U, V) ≤ ∫ |x - y|² H(x y, (1 - x)(1 - y)) dx dy`. -/
theorem lintegral_le_lintegral_rootMap (H : ℂ × ℂ → ℝ≥0∞) :
    ∫⁻ p, H p ≤ ∫⁻ q, ENNReal.ofReal (Complex.normSq (q.1 - q.2)) * H (rootMap q) := by
  set s : Set (ℂ × ℂ) := {q | q.1 ≠ q.2}
  have hs : MeasurableSet s := (measurableSet_eq_fun measurable_fst measurable_snd).compl
  have hf' : ∀ q ∈ s, HasFDerivWithinAt rootMap
      ((LinearMap.toContinuousLinearMap (lin2 q.2 q.1 (-(1 - q.2)) (-(1 - q.1)))).restrictScalars
        ℝ) s q := fun q _ => ((hasFDerivAt_rootMap q).restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ q ∈ s, ((LinearMap.toContinuousLinearMap
      (lin2 q.2 q.1 (-(1 - q.2)) (-(1 - q.1)))).restrictScalars ℝ).det ≠ 0 := fun q hq => by
    rw [det_rootMap]; exact (Complex.normSq_pos.mpr (sub_ne_zero.mpr hq)).ne'
  have key := lintegral_image_le_lintegral_abs_det_fderiv_mul volume hs hf' hdet H
  have hae : ∀ᵐ p ∂(volume : Measure (ℂ × ℂ)), p ∈ {p | refQ p ≠ 0} := by
    refine ae_iff.mpr ?_
    simpa using volume_refQ_eq_zero
  calc ∫⁻ p, H p = ∫⁻ p in {p | refQ p ≠ 0}, H p := by
        rw [Measure.restrict_eq_self_of_ae_mem hae]
    _ ≤ ∫⁻ p in rootMap '' s, H p := lintegral_mono_set fun p hp => mem_image_rootMap hp
    _ ≤ _ := key
    _ ≤ ∫⁻ q, ENNReal.ofReal (Complex.normSq (q.1 - q.2)) * H (rootMap q) := by
        refine (setLIntegral_le_lintegral _ _).trans (le_of_eq (lintegral_congr fun q => ?_))
        rw [det_rootMap, abs_of_nonneg (Complex.normSq_nonneg _)]

/-! ### The weighted reference fibre -/

/-- The two-cube density `|𝔇(P)|^{-4/3}` (`∞` where `𝔇 = 0`). -/
noncomputable def twoCubeDensity (P : Cubic) : ℝ≥0∞ := ((‖disc P‖₊ : ℝ≥0∞)⁻¹) ^ (4 / 3 : ℝ)

/-- The two-cube density is measurable. -/
@[fun_prop] theorem measurable_twoCubeDensity : Measurable twoCubeDensity := by
  unfold twoCubeDensity disc; fun_prop

/-- The weighted reference fibre `∫ ‖u‖^β |𝔇(P* - u³)|^{-4/3} du`. -/
noncomputable def refFibre (β : ℝ) : ℝ≥0∞ :=
  ∫⁻ u : Form, ENNReal.ofReal (‖u‖ ^ β) * twoCubeDensity (refCubic - cube u)

/-- `(‖z‖₊⁻¹)^{a} = ‖z‖ₑ^{-a}`. -/
theorem inv_nnnorm_rpow (z : ℂ) (a : ℝ) : ((‖z‖₊ : ℝ≥0∞)⁻¹) ^ a = ‖z‖ₑ ^ (-a) := by
  rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]; rfl

/-- The reference weight bound `max(|x y|, |(1 - x)(1 - y)|) ≤ (1 + |x|)(1 + |y|)`. -/
theorem max_norm_rootMap_le (x y : ℂ) :
    max ‖x * y‖ ‖(1 - x) * (1 - y)‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
  have h1 : ‖1 - x‖ ≤ 1 + ‖x‖ := by
    calc ‖1 - x‖ ≤ ‖(1 : ℂ)‖ + ‖x‖ := norm_sub_le _ _
      _ = 1 + ‖x‖ := by rw [norm_one]
  have h2 : ‖1 - y‖ ≤ 1 + ‖y‖ := by
    calc ‖1 - y‖ ≤ ‖(1 : ℂ)‖ + ‖y‖ := norm_sub_le _ _
      _ = 1 + ‖y‖ := by rw [norm_one]
  rw [norm_mul, norm_mul]
  refine max_le ?_ ?_
  · gcongr <;> linarith [norm_nonneg x, norm_nonneg y]
  · gcongr

/-- The pointwise bound after both substitutions. -/
theorem rootMap_integrand_le {β : ℝ} (hβ : 0 ≤ β) (q : ℂ × ℂ) (hxy : q.1 ≠ q.2)
    (hx0 : q.1 ≠ 0) (hx1 : q.1 ≠ 1) (hy0 : q.2 ≠ 0) (hy1 : q.2 ≠ 1) :
    ENNReal.ofReal (Complex.normSq (q.1 - q.2)) *
        (ENNReal.ofReal (max ‖(rootMap q).1‖ ‖(rootMap q).2‖ ^ (β / 3)) *
          ((‖refQ (rootMap q)‖₊ : ℝ≥0∞)⁻¹) ^ (4 / 3 : ℝ) *
          (‖(rootMap q).1‖ₑ ^ (-(4 / 3 : ℝ)) * ‖(rootMap q).2‖ₑ ^ (-(4 / 3 : ℝ)))) ≤
      refWeight β q.1 * refWeight β q.2 * ‖q.1 - q.2‖ₑ ^ (-(2 / 3 : ℝ)) := by
  rw [refQ_rootMap]
  obtain ⟨x, y⟩ := q
  simp only [rootMap] at hxy hx0 hx1 hy0 hy1 ⊢
  have hd : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have h1x : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have h1y : 1 - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy1)
  -- the weight
  have hw : ENNReal.ofReal (max ‖x * y‖ ‖(1 - x) * (1 - y)‖ ^ (β / 3)) ≤
      ENNReal.ofReal ((1 + ‖x‖) ^ (β / 3)) * ENNReal.ofReal ((1 + ‖y‖) ^ (β / 3)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (by positivity) (max_norm_rootMap_le x y) (by positivity))
  -- the singular factors
  have e1 : ENNReal.ofReal (Complex.normSq (x - y)) * ((‖(x - y) ^ 2‖₊ : ℝ≥0∞)⁻¹) ^ (4 / 3 : ℝ) =
      ‖x - y‖ₑ ^ (-(2 / 3 : ℝ)) := by
    rw [inv_nnnorm_rpow, Complex.normSq_eq_norm_sq, ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm, enorm_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add _ _ (enorm_ne_zero.mpr hd) enorm_ne_top]
    norm_num
  have e2 : ‖x * y‖ₑ ^ (-(4 / 3 : ℝ)) = ‖x‖ₑ ^ (-(4 / 3 : ℝ)) * ‖y‖ₑ ^ (-(4 / 3 : ℝ)) := by
    rw [enorm_mul, ENNReal.mul_rpow_of_ne_zero (enorm_ne_zero.mpr hx0) (enorm_ne_zero.mpr hy0)]
  have e3 : ‖(1 - x) * (1 - y)‖ₑ ^ (-(4 / 3 : ℝ)) =
      ‖1 - x‖ₑ ^ (-(4 / 3 : ℝ)) * ‖1 - y‖ₑ ^ (-(4 / 3 : ℝ)) := by
    rw [enorm_mul, ENNReal.mul_rpow_of_ne_zero (enorm_ne_zero.mpr h1x) (enorm_ne_zero.mpr h1y)]
  set W := ENNReal.ofReal (max ‖x * y‖ ‖(1 - x) * (1 - y)‖ ^ (β / 3))
  calc ENNReal.ofReal (Complex.normSq (x - y)) *
        (W * ((‖(x - y) ^ 2‖₊ : ℝ≥0∞)⁻¹) ^ (4 / 3 : ℝ) *
          (‖x * y‖ₑ ^ (-(4 / 3 : ℝ)) * ‖(1 - x) * (1 - y)‖ₑ ^ (-(4 / 3 : ℝ))))
      = W * (ENNReal.ofReal (Complex.normSq (x - y)) *
          ((‖(x - y) ^ 2‖₊ : ℝ≥0∞)⁻¹) ^ (4 / 3 : ℝ)) *
          (‖x * y‖ₑ ^ (-(4 / 3 : ℝ)) * ‖(1 - x) * (1 - y)‖ₑ ^ (-(4 / 3 : ℝ))) := by ring
    _ = W * ‖x - y‖ₑ ^ (-(2 / 3 : ℝ)) * ((‖x‖ₑ ^ (-(4 / 3 : ℝ)) * ‖y‖ₑ ^ (-(4 / 3 : ℝ))) *
          (‖1 - x‖ₑ ^ (-(4 / 3 : ℝ)) * ‖1 - y‖ₑ ^ (-(4 / 3 : ℝ)))) := by rw [e1, e2, e3]
    _ ≤ (ENNReal.ofReal ((1 + ‖x‖) ^ (β / 3)) * ENNReal.ofReal ((1 + ‖y‖) ^ (β / 3))) *
          ‖x - y‖ₑ ^ (-(2 / 3 : ℝ)) * ((‖x‖ₑ ^ (-(4 / 3 : ℝ)) * ‖y‖ₑ ^ (-(4 / 3 : ℝ))) *
          (‖1 - x‖ₑ ^ (-(4 / 3 : ℝ)) * ‖1 - y‖ₑ ^ (-(4 / 3 : ℝ)))) := by gcongr
    _ = refWeight β x * refWeight β y * ‖x - y‖ₑ ^ (-(2 / 3 : ℝ)) := by
        simp only [refWeight]; ring

/-- Lines `{x = c}` and `{y = c}` and the diagonal are null in `ℂ²`. -/
theorem ae_generic_pair : ∀ᵐ q : ℂ × ℂ, q.1 ≠ q.2 ∧ q.1 ≠ 0 ∧ q.1 ≠ 1 ∧ q.2 ≠ 0 ∧ q.2 ≠ 1 := by
  rw [Measure.volume_eq_prod]
  have hfst : ∀ c : ℂ, ∀ᵐ q : ℂ × ℂ ∂(volume.prod volume), q.1 ≠ c := fun c =>
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume c)
  have hsnd : ∀ c : ℂ, ∀ᵐ q : ℂ × ℂ ∂(volume.prod volume), q.2 ≠ c := fun c =>
    Measure.quasiMeasurePreserving_snd.ae (Measure.ae_ne volume c)
  have hdiag : ∀ᵐ q : ℂ × ℂ ∂(volume.prod volume), q.1 ≠ q.2 := by
    refine ae_iff.mpr ?_
    simp only [ne_eq, not_not]
    rw [Measure.measure_prod_null (measurableSet_eq_fun measurable_fst measurable_snd)]
    refine Filter.Eventually.of_forall fun x => ?_
    change volume (Prod.mk x ⁻¹' {q : ℂ × ℂ | q.1 = q.2}) = 0
    refine measure_mono_null (fun y hy => ?_) (measure_singleton x)
    exact hy.symm
  filter_upwards [hdiag, hfst 0, hfst 1, hsnd 0, hsnd 1] with q h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **The weighted reference fibre is finite** for `0 ≤ β < 2` (the note's `ρ_β(P*) < ∞`). -/
theorem refFibre_lt_top {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 2) : refFibre β < ∞ := by
  set G : ℂ × ℂ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (max ‖p.1‖ ‖p.2‖ ^ (β / 3)) * ((‖refQ p‖₊ : ℝ≥0∞)⁻¹) ^ (4 / 3 : ℝ)
  have hG : Measurable G := by simp only [G, refQ]; fun_prop
  -- step 1: the integrand is `G (u₁³, u₂³)`
  have step1 : refFibre β = ∫⁻ u : Form, G (u.1 ^ 3, u.2 ^ 3) := by
    refine lintegral_congr fun u => ?_
    simp only [G, twoCubeDensity]
    congr 2
    · rw [norm_pow, norm_pow, Prod.norm_def]
      rcases le_total ‖u.1‖ ‖u.2‖ with h | h
      · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ (norm_nonneg _) h 3),
          ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        congr 1; push_cast; ring
      · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ (norm_nonneg _) h 3),
          ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        congr 1; push_cast; ring
    · rw [disc_refCubic_sub_cube]; simp only [refQ]
  set Φ : ℂ → ℝ≥0∞ := fun U => ∫⁻ V, G (U, V) * ‖V‖ₑ ^ (-(4 / 3 : ℝ))
  have hΦ : Measurable Φ := (by fun_prop : Measurable fun p : ℂ × ℂ =>
    G p * ‖p.2‖ₑ ^ (-(4 / 3 : ℝ))).lintegral_prod_right'
  set H : ℂ × ℂ → ℝ≥0∞ := fun p =>
    G p * (‖p.1‖ₑ ^ (-(4 / 3 : ℝ)) * ‖p.2‖ₑ ^ (-(4 / 3 : ℝ)))
  have hH : Measurable H := by fun_prop
  calc refFibre β = ∫⁻ u : Form, G (u.1 ^ 3, u.2 ^ 3) := step1
    _ = ∫⁻ u₁, ∫⁻ u₂, G (u₁ ^ 3, u₂ ^ 3) := by
        rw [Measure.volume_eq_prod, lintegral_prod _ (by fun_prop)]
    _ ≤ ∫⁻ u₁, 3⁻¹ * Φ (u₁ ^ 3) :=
        lintegral_mono fun u₁ => lintegral_comp_cube_le (φ := fun V => G (u₁ ^ 3, V)) (by fun_prop)
    _ = 3⁻¹ * ∫⁻ u₁, Φ (u₁ ^ 3) := lintegral_const_mul _ (by fun_prop)
    _ ≤ 3⁻¹ * (3⁻¹ * ∫⁻ U, Φ U * ‖U‖ₑ ^ (-(4 / 3 : ℝ))) := by
        gcongr; exact lintegral_comp_cube_le hΦ
    _ = 3⁻¹ * (3⁻¹ * ∫⁻ p, H p) := by
        congr 2
        rw [Measure.volume_eq_prod, lintegral_prod _ hH.aemeasurable]
        refine lintegral_congr fun U => ?_
        rw [← lintegral_mul_const _ (by fun_prop)]
        refine lintegral_congr fun V => ?_
        simp only [H]; ring
    _ ≤ 3⁻¹ * (3⁻¹ * ∫⁻ q, ENNReal.ofReal (Complex.normSq (q.1 - q.2)) * H (rootMap q)) := by
        gcongr 3⁻¹ * (3⁻¹ * ?_); exact lintegral_le_lintegral_rootMap H
    _ ≤ 3⁻¹ * (3⁻¹ * ∫⁻ q : ℂ × ℂ, refWeight β q.1 * refWeight β q.2 *
          ‖q.1 - q.2‖ₑ ^ (-(2 / 3 : ℝ))) := by
        gcongr 3⁻¹ * (3⁻¹ * ?_)
        refine lintegral_mono_ae ?_
        filter_upwards [ae_generic_pair] with q ⟨h1, h2, h3, h4, h5⟩
        exact rootMap_integrand_le hβ0 q h1 h2 h3 h4 h5
    _ < ∞ := by
        refine ENNReal.mul_lt_top (by simp) (ENNReal.mul_lt_top (by simp) ?_)
        rw [Measure.volume_eq_prod, lintegral_prod _ (by fun_prop)]
        exact lintegral_refBilinear_lt_top hβ0 hβ

end SLT.PositionFour
