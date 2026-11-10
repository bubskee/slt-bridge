/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Upstream.Cusp
public import SLT.PositionFour.Upstream.Density
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Local finiteness (note §1, "Local finiteness"; step 5)

`locallyFiniteRow`: for `0 ≤ β < 2`, `rowMeasure β` is finite on closed balls.

Route: `DensityBound` plus local integrability of `densityBound β`. On a ball both summands of
`densityBound β` are at most a constant times `|𝔇|^{-4/3}` (`densityBound_le_on_ball`, using
`1 + β/6 < 4/3`), so it suffices that `|𝔇|^{-4/3}` is integrable on balls
(`lintegral_closedBall_twoCubeDensity_lt_top`). This departs from the note's chart in one respect:
instead of the cusp normal form `𝔇 = 4q³ + r²` at `P₀ = 1` plus homogeneity at `0`, it uses one
cone chart `{‖P‖ ≤ C |P₀|}` through the origin:

1. as a quadratic in `P₃`, `𝔇 = P₀² P₃² + B P₃ + C'` with discriminant `16 (P₁² - P₀P₂)³`, so the
   full-plane integral in `P₃` is `≍ |P₀|^{-4/3} |P₁² - P₀P₂|^{-1}` (`lintegral_last_le`);
2. the `P₂`-integral over `|P₂| ≤ C|P₀|` is `≲ |P₀|^{-4/3}` (shifted disc), and the `P₁`-integral
   gives `|P₀|^{2/3}`, bounded (`lintegral_chart_lt_top`);
3. four substitutions `g ∈ GL₂` with `|det g| = 1` (identity, `s ↔ t`, `t ↦ s ± t`) move any cubic
   into the chart, because `‖P‖ ≤ max(|P(1,0)|, |P(0,1)|, |P(1,1)|, |P(1,-1)|)`
   (`norm_le_max_eval`);
   they preserve `𝔇` and Lebesgue measure (`det_cubicActL`: `det_ℂ = det(g)⁶`).
-/

@[expose] public section

namespace SLT.PositionFour

open MeasureTheory Set Metric
open scoped ENNReal

/-! ### Coordinates with the last moment separated -/

/-- Cubic space in the coordinates `(((P₀, P₁), P₂), P₃)`, as an equivalence. -/
def cubicEquiv3Fun : Cubic ≃ ((ℂ × ℂ) × ℂ) × ℂ where
  toFun P := (((P 0, P 1), P 2), P 3)
  invFun x := ![x.1.1.1, x.1.1.2, x.1.2, x.2]
  left_inv P := by ext i; fin_cases i <;> rfl
  right_inv _ := rfl

/-- Cubic space in the coordinates `(((P₀, P₁), P₂), P₃)`. -/
def cubicEquiv3 : Cubic ≃ᵐ ((ℂ × ℂ) × ℂ) × ℂ where
  toEquiv := cubicEquiv3Fun
  measurable_toFun := by
    change Measurable fun P : Cubic => (((P 0, P 1), P 2), P 3)
    fun_prop
  measurable_invFun := by
    change Measurable fun x : ((ℂ × ℂ) × ℂ) × ℂ => (![x.1.1.1, x.1.1.2, x.1.2, x.2] : Cubic)
    refine measurable_pi_iff.mpr fun i => ?_
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, Fin.isValue] <;> fun_prop

/-- `cubicEquiv3` evaluated. -/
@[simp] theorem cubicEquiv3_apply (P : Cubic) : cubicEquiv3 P = (((P 0, P 1), P 2), P 3) := rfl

/-- `cubicEquiv3.symm` evaluated. -/
@[simp] theorem cubicEquiv3_symm_apply (x : ((ℂ × ℂ) × ℂ) × ℂ) :
    cubicEquiv3.symm x = ![x.1.1.1, x.1.1.2, x.1.2, x.2] := rfl

/-- Lebesgue measure on cubic space is the product measure in `(((P₀, P₁), P₂), P₃)`. -/
theorem measurePreserving_cubicEquiv3 : MeasurePreserving cubicEquiv3 := by
  have h : MeasurePreserving cubicEquiv3.symm := by
    refine ⟨cubicEquiv3.symm.measurable, ?_⟩
    rw [volume_pi]
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [MeasurableEquiv.map_apply]
    have : cubicEquiv3.symm ⁻¹' univ.pi s = ((s 0 ×ˢ s 1) ×ˢ s 2) ×ˢ s 3 := by
      ext x
      simp only [mem_preimage, mem_univ_pi, mem_prod]
      constructor
      · intro h; exact ⟨⟨⟨h 0, h 1⟩, h 2⟩, h 3⟩
      · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ i
        fin_cases i
        exacts [h0, h1, h2, h3]
    rw [this, Measure.volume_eq_prod ((ℂ × ℂ) × ℂ) ℂ, Measure.prod_prod,
      Measure.volume_eq_prod (ℂ × ℂ) ℂ, Measure.prod_prod, Measure.volume_eq_prod ℂ ℂ,
      Measure.prod_prod, Fin.prod_univ_four]
  simpa using h.symm

/-! ### The last-coordinate integral -/

/-- `𝔇` as a quadratic in `P₃`. -/
theorem disc_eq_quadratic (P : Cubic) :
    disc P = P 0 ^ 2 * P 3 ^ 2 + (4 * P 1 ^ 3 - 6 * P 0 * P 1 * P 2) * P 3 +
      (4 * P 0 * P 2 ^ 3 - 3 * P 1 ^ 2 * P 2 ^ 2) := by
  simp only [disc]; ring

/-- The discriminant of `𝔇` in `P₃` is `16 (P₁² - P₀P₂)³`. -/
theorem discr_disc (q0 q1 q2 : ℂ) :
    (4 * q1 ^ 3 - 6 * q0 * q1 * q2) ^ 2 - 4 * q0 ^ 2 * (4 * q0 * q2 ^ 3 - 3 * q1 ^ 2 * q2 ^ 2) =
      16 * (q1 ^ 2 - q0 * q2) ^ 3 := by
  ring

/-- The constant of `lintegral_last_le`. -/
noncomputable def lastConst : ℝ≥0∞ :=
  ENNReal.ofReal (4 ^ (1 / 3 : ℝ) * 16 ^ (-(1 / 3 : ℝ))) * quadConst + 1

/-- `rpow` of an `enorm` with negative exponent is nonzero. -/
theorem enorm_rpow_neg_ne_zero (z : ℂ) {a : ℝ} (ha : 0 < a) : ‖z‖ₑ ^ (-a) ≠ 0 := by
  rw [Ne, ENNReal.rpow_eq_zero_iff]
  push Not
  exact ⟨fun _ => by linarith, fun h => absurd h enorm_ne_top⟩

/-- `‖0‖ₑ ^ (-a) = ∞` for `a > 0`. -/
theorem enorm_zero_rpow_neg {a : ℝ} (ha : 0 < a) : ‖(0 : ℂ)‖ₑ ^ (-a) = ⊤ := by
  rw [enorm_zero, ENNReal.zero_rpow_of_neg (by linarith)]

/-- **The `P₃`-integral.** `∫ |𝔇(q₀, q₁, q₂, v)|^{-4/3} dv ≲ |q₀|^{-4/3} |q₁² - q₀q₂|^{-1}`. -/
theorem lintegral_last_le (q0 q1 q2 : ℂ) :
    ∫⁻ v : ℂ, twoCubeDensity ![q0, q1, q2, v] ≤
      lastConst * (‖q0‖ₑ ^ (-(4 / 3 : ℝ)) * ‖q1 ^ 2 - q0 * q2‖ₑ ^ (-(1 : ℝ))) := by
  have hL : lastConst ≠ 0 := by simp [lastConst]
  by_cases h0 : q0 = 0
  · rw [h0, enorm_zero_rpow_neg (by norm_num), ENNReal.top_mul
      (enorm_rpow_neg_ne_zero _ (by norm_num)), ENNReal.mul_top hL]
    exact le_top
  by_cases hX : q1 ^ 2 - q0 * q2 = 0
  · rw [hX, enorm_zero_rpow_neg (by norm_num), ENNReal.mul_top
      (enorm_rpow_neg_ne_zero _ (by norm_num)), ENNReal.mul_top hL]
    exact le_top
  have hA : q0 ^ 2 ≠ 0 := pow_ne_zero 2 h0
  have hΔ : (4 * q1 ^ 3 - 6 * q0 * q1 * q2) ^ 2 - 4 * q0 ^ 2 * (4 * q0 * q2 ^ 3 -
      3 * q1 ^ 2 * q2 ^ 2) ≠ 0 := by
    rw [discr_disc]; exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hX)
  have hq := lintegral_quadratic_eq hA hΔ
  have hint : ∫⁻ v : ℂ, twoCubeDensity ![q0, q1, q2, v] =
      ∫⁻ v : ℂ, ‖q0 ^ 2 * v ^ 2 + (4 * q1 ^ 3 - 6 * q0 * q1 * q2) * v +
        (4 * q0 * q2 ^ 3 - 3 * q1 ^ 2 * q2 ^ 2)‖ₑ ^ (-(4 / 3 : ℝ)) := by
    refine lintegral_congr fun v => ?_
    rw [twoCubeDensity, inv_nnnorm_rpow, disc_eq_quadratic]
    rfl
  rw [hint, hq, discr_disc]
  have h0n : 0 < ‖q0‖ := norm_pos_iff.mpr h0
  have hXn : 0 < ‖q1 ^ 2 - q0 * q2‖ := norm_pos_iff.mpr hX
  have hreal : 4 ^ (1 / 3 : ℝ) * ‖q0 ^ 2‖ ^ (-(2 / 3 : ℝ)) *
      ‖16 * (q1 ^ 2 - q0 * q2) ^ 3‖ ^ (-(1 / 3 : ℝ)) =
      (4 ^ (1 / 3 : ℝ) * 16 ^ (-(1 / 3 : ℝ))) *
        (‖q0‖ ^ (-(4 / 3 : ℝ)) * ‖q1 ^ 2 - q0 * q2‖ ^ (-(1 : ℝ))) := by
    rw [norm_pow, norm_mul, norm_pow, Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_natCast ‖q0‖ 2, ← Real.rpow_mul h0n.le,
      ← Real.rpow_natCast ‖q1 ^ 2 - q0 * q2‖ 3, ← Real.rpow_mul hXn.le]
    norm_num
    ring
  rw [hreal, ENNReal.ofReal_mul (p := 4 ^ (1 / 3 : ℝ) * 16 ^ (-(1 / 3 : ℝ))) (by positivity),
    ENNReal.ofReal_mul (p := ‖q0‖ ^ (-(4 / 3 : ℝ))) (by positivity),
    ← enorm_rpow_eq_ofReal h0, ← enorm_rpow_eq_ofReal hX]
  calc ENNReal.ofReal (4 ^ (1 / 3 : ℝ) * 16 ^ (-(1 / 3 : ℝ))) *
        (‖q0‖ₑ ^ (-(4 / 3 : ℝ)) * ‖q1 ^ 2 - q0 * q2‖ₑ ^ (-(1 : ℝ))) * quadConst
      = (ENNReal.ofReal (4 ^ (1 / 3 : ℝ) * 16 ^ (-(1 / 3 : ℝ))) * quadConst) *
        (‖q0‖ₑ ^ (-(4 / 3 : ℝ)) * ‖q1 ^ 2 - q0 * q2‖ₑ ^ (-(1 : ℝ))) := by ring
    _ ≤ _ := by gcongr; exact le_self_add

/-! ### The cone chart -/

/-- The cone chart `{‖P‖ ≤ R, ‖P‖ ≤ C |P₀|}`. -/
def chart (C R : ℝ) : Set Cubic := {P | ‖P‖ ≤ R ∧ ‖P‖ ≤ C * ‖P 0‖}

/-- The chart is measurable. -/
theorem measurableSet_chart (C R : ℝ) : MeasurableSet (chart C R) :=
  (measurableSet_le measurable_norm measurable_const).inter
    (measurableSet_le measurable_norm (by fun_prop))

/-- The `P₂`-integral: for `q₀ ≠ 0`,
`∫_{|q₂| ≤ C|q₀|} |q₁² - q₀ q₂|^{-1} dq₂ ≤ L C`. -/
theorem lintegral_middle_le {q0 : ℂ} (h0 : q0 ≠ 0) (q1 : ℂ) {C : ℝ} (hC : 0 < C) :
    ∫⁻ q2 in closedBall (0 : ℂ) (C * ‖q0‖), ‖q1 ^ 2 - q0 * q2‖ₑ ^ (-(1 : ℝ)) ≤
      discConst * ENNReal.ofReal C := by
  have h0n : 0 < ‖q0‖ := norm_pos_iff.mpr h0
  have hfac : ∀ q2 : ℂ, ‖q1 ^ 2 - q0 * q2‖ₑ ^ (-(1 : ℝ)) =
      ‖q0‖ₑ ^ (-(1 : ℝ)) * ‖q2 - q1 ^ 2 / q0‖ₑ ^ (-(1 : ℝ)) := by
    intro q2
    rw [show q1 ^ 2 - q0 * q2 = -(q0 * (q2 - q1 ^ 2 / q0)) by field_simp; ring, enorm_neg,
      enorm_mul, ENNReal.mul_rpow_of_ne_top enorm_ne_top enorm_ne_top]
  simp_rw [hfac]
  rw [lintegral_const_mul _ (by fun_prop)]
  calc ‖q0‖ₑ ^ (-(1 : ℝ)) * ∫⁻ q2 in closedBall (0 : ℂ) (C * ‖q0‖), ‖q2 - q1 ^ 2 / q0‖ₑ ^ (-(1 : ℝ))
      ≤ ‖q0‖ₑ ^ (-(1 : ℝ)) * (discConst * ENNReal.ofReal (C * ‖q0‖)) := by
        gcongr; exact lintegral_closedBall_rpow_sub_le _ (by positivity)
    _ = discConst * ENNReal.ofReal C := by
        rw [enorm_rpow_eq_ofReal h0, ENNReal.ofReal_mul hC.le, Real.rpow_neg_one]
        rw [show ENNReal.ofReal ‖q0‖⁻¹ * (discConst * (ENNReal.ofReal C * ENNReal.ofReal ‖q0‖)) =
          discConst * ENNReal.ofReal C * (ENNReal.ofReal ‖q0‖⁻¹ * ENNReal.ofReal ‖q0‖) by ring,
          ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ h0n.ne', ENNReal.ofReal_one,
          mul_one]

/-- The `P₀`-integrand after the `P₁`-integral: `|q₀|^{-4/3} (C |q₀|)² ≤ C² R^{2/3}` on
`|q₀| ≤ R`. -/
theorem enorm_rpow_mul_sq_le {q0 : ℂ} {C R : ℝ} (hC : 0 ≤ C) (hq : ‖q0‖ ≤ R) :
    ‖q0‖ₑ ^ (-(4 / 3 : ℝ)) * ENNReal.ofReal (C * ‖q0‖) ^ 2 ≤
      ENNReal.ofReal (C ^ 2 * R ^ (2 / 3 : ℝ)) := by
  by_cases h0 : q0 = 0
  · simp [h0]
  have h0n : 0 < ‖q0‖ := norm_pos_iff.mpr h0
  rw [enorm_rpow_eq_ofReal h0, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : ‖q0‖ ^ (-(4 / 3 : ℝ)) * (C * ‖q0‖) ^ 2 = C ^ 2 * ‖q0‖ ^ (2 / 3 : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast ‖q0‖ 2]
    rw [show ‖q0‖ ^ (-(4 / 3 : ℝ)) * (C ^ 2 * ‖q0‖ ^ ((2 : ℕ) : ℝ)) =
      C ^ 2 * (‖q0‖ ^ (-(4 / 3 : ℝ)) * ‖q0‖ ^ ((2 : ℕ) : ℝ)) by ring, ← Real.rpow_add h0n]
    norm_num
  rw [this]
  gcongr

/-- **The chart integral.** `∫_{‖P‖ ≤ R, ‖P‖ ≤ C|P₀|} |𝔇(P)|^{-4/3} dP < ∞` for `C ≥ 1`. -/
theorem lintegral_chart_lt_top {C : ℝ} (hC : 1 ≤ C) (R : ℝ) :
    ∫⁻ P, (chart C R).indicator twoCubeDensity P < ∞ := by
  have hC0 : 0 < C := by linarith
  set S' : Set (ℂ × ℂ) := {y | ‖y.1‖ ≤ R ∧ ‖y.2‖ ≤ C * ‖y.1‖}
  set S : Set ((ℂ × ℂ) × ℂ) := {x | x.1 ∈ S' ∧ ‖x.2‖ ≤ C * ‖x.1.1‖}
  have hS' : MeasurableSet S' := by
    have h1 : MeasurableSet {y : ℂ × ℂ | ‖y.1‖ ≤ R} := measurableSet_le (by fun_prop) (by fun_prop)
    have h2 : MeasurableSet {y : ℂ × ℂ | ‖y.2‖ ≤ C * ‖y.1‖} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    exact h1.inter h2
  have hS : MeasurableSet S := by
    have h2 : MeasurableSet {x : (ℂ × ℂ) × ℂ | ‖x.2‖ ≤ C * ‖x.1.1‖} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    exact (measurable_fst hS').inter h2
  set M : ℝ≥0∞ := lastConst * (discConst * ENNReal.ofReal C)
  have hM : M < ∞ := by
    refine ENNReal.mul_lt_top ?_ (ENNReal.mul_lt_top discConst_lt_top ENNReal.ofReal_lt_top)
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top quadConst_lt_top,
      ENNReal.one_lt_top⟩
  -- step a: the chart lies over `S`
  have hpt : ∀ P : Cubic, (chart C R).indicator twoCubeDensity P ≤
      S.indicator 1 (cubicEquiv3 P).1 * twoCubeDensity P := by
    intro P
    by_cases hP : P ∈ chart C R
    · have h0 : ‖P 0‖ ≤ ‖P‖ := norm_le_pi_norm P 0
      have h1 : ‖P 1‖ ≤ ‖P‖ := norm_le_pi_norm P 1
      have h2 : ‖P 2‖ ≤ ‖P‖ := norm_le_pi_norm P 2
      have hmem : (cubicEquiv3 P).1 ∈ S :=
        ⟨⟨by simp only [cubicEquiv3_apply]; linarith [hP.1],
          by simp only [cubicEquiv3_apply]; linarith [hP.2]⟩,
          by simp only [cubicEquiv3_apply]; linarith [hP.2]⟩
      rw [indicator_of_mem hP, indicator_of_mem hmem, Pi.one_apply, one_mul]
    · rw [indicator_of_notMem hP]; exact zero_le
  have hF : Measurable fun p : ((ℂ × ℂ) × ℂ) × ℂ =>
      S.indicator 1 p.1 * twoCubeDensity (cubicEquiv3.symm p) :=
    ((measurable_one.indicator hS).comp measurable_fst).mul
      (measurable_twoCubeDensity.comp cubicEquiv3.symm.measurable)
  calc ∫⁻ P, (chart C R).indicator twoCubeDensity P
      ≤ ∫⁻ P, S.indicator 1 (cubicEquiv3 P).1 * twoCubeDensity (cubicEquiv3.symm (cubicEquiv3 P)) :=
        lintegral_mono fun P => by rw [cubicEquiv3.symm_apply_apply]; exact hpt P
    _ = ∫⁻ p, S.indicator 1 p.1 * twoCubeDensity (cubicEquiv3.symm p) :=
        measurePreserving_cubicEquiv3.lintegral_comp_emb cubicEquiv3.measurableEmbedding
          (fun p => S.indicator 1 p.1 * twoCubeDensity (cubicEquiv3.symm p))
    _ = ∫⁻ x, S.indicator 1 x * ∫⁻ v, twoCubeDensity ![x.1.1, x.1.2, x.2, v] := by
        rw [Measure.volume_eq_prod, lintegral_prod _ hF.aemeasurable]
        refine lintegral_congr fun x => ?_
        change ∫⁻ v, S.indicator 1 x * twoCubeDensity ![x.1.1, x.1.2, x.2, v] = _
        exact lintegral_const_mul _ (by fun_prop)
    _ ≤ ∫⁻ x, S.indicator 1 x *
          (lastConst * (‖x.1.1‖ₑ ^ (-(4 / 3 : ℝ)) * ‖x.1.2 ^ 2 - x.1.1 * x.2‖ₑ ^ (-(1 : ℝ)))) := by
        gcongr with x; exact lintegral_last_le _ _ _
    _ = ∫⁻ y, ∫⁻ q2, S.indicator 1 (y, q2) *
          (lastConst * (‖y.1‖ₑ ^ (-(4 / 3 : ℝ)) * ‖y.2 ^ 2 - y.1 * q2‖ₑ ^ (-(1 : ℝ)))) := by
        rw [Measure.volume_eq_prod, lintegral_prod _ (by fun_prop)]
    _ ≤ ∫⁻ y, S'.indicator 1 y * (M * ‖y.1‖ₑ ^ (-(4 / 3 : ℝ))) := by
        refine lintegral_mono_ae ?_
        filter_upwards [Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0 : ℂ))]
          with y hy
        have hsplit : ∀ q2 : ℂ, S.indicator (1 : (ℂ × ℂ) × ℂ → ℝ≥0∞) (y, q2) =
            S'.indicator (1 : ℂ × ℂ → ℝ≥0∞) y *
              (closedBall (0 : ℂ) (C * ‖y.1‖)).indicator (1 : ℂ → ℝ≥0∞) q2 := by
          intro q2
          have hmem : (y, q2) ∈ S ↔ y ∈ S' ∧ q2 ∈ closedBall (0 : ℂ) (C * ‖y.1‖) := by
            rw [mem_closedBall_zero_iff]; exact Iff.rfl
          by_cases h1 : y ∈ S'
          · by_cases h2 : q2 ∈ closedBall (0 : ℂ) (C * ‖y.1‖)
            · rw [indicator_of_mem (hmem.mpr ⟨h1, h2⟩), indicator_of_mem h1,
                indicator_of_mem h2]; simp
            · rw [indicator_of_notMem (fun h => h2 (hmem.mp h).2), indicator_of_notMem h2,
                mul_zero]
          · rw [indicator_of_notMem (fun h => h1 (hmem.mp h).1), indicator_of_notMem h1, zero_mul]
        simp_rw [hsplit]
        have hrw : ∀ q2 : ℂ, S'.indicator (1 : ℂ × ℂ → ℝ≥0∞) y *
            (closedBall (0 : ℂ) (C * ‖y.1‖)).indicator (1 : ℂ → ℝ≥0∞) q2 *
            (lastConst * (‖y.1‖ₑ ^ (-(4 / 3 : ℝ)) * ‖y.2 ^ 2 - y.1 * q2‖ₑ ^ (-(1 : ℝ)))) =
            (S'.indicator 1 y * lastConst * ‖y.1‖ₑ ^ (-(4 / 3 : ℝ))) *
              (closedBall (0 : ℂ) (C * ‖y.1‖)).indicator
                (fun q2 => ‖y.2 ^ 2 - y.1 * q2‖ₑ ^ (-(1 : ℝ))) q2 := by
          intro q2
          by_cases h2 : q2 ∈ closedBall (0 : ℂ) (C * ‖y.1‖)
          · simp only [indicator_of_mem h2, Pi.one_apply]; ring
          · simp only [indicator_of_notMem h2, mul_zero, zero_mul]
        simp_rw [hrw]
        rw [lintegral_const_mul _ ((by fun_prop : Measurable fun q2 : ℂ =>
            ‖y.2 ^ 2 - y.1 * q2‖ₑ ^ (-(1 : ℝ))).indicator measurableSet_closedBall),
          lintegral_indicator measurableSet_closedBall]
        calc S'.indicator 1 y * lastConst * ‖y.1‖ₑ ^ (-(4 / 3 : ℝ)) *
              ∫⁻ q2 in closedBall (0 : ℂ) (C * ‖y.1‖), ‖y.2 ^ 2 - y.1 * q2‖ₑ ^ (-(1 : ℝ))
            ≤ S'.indicator 1 y * lastConst * ‖y.1‖ₑ ^ (-(4 / 3 : ℝ)) *
                (discConst * ENNReal.ofReal C) := by
              gcongr; exact lintegral_middle_le hy _ hC0
          _ = S'.indicator 1 y * (M * ‖y.1‖ₑ ^ (-(4 / 3 : ℝ))) := by simp only [M]; ring
    _ = ∫⁻ q0, ∫⁻ q1, S'.indicator 1 (q0, q1) * (M * ‖q0‖ₑ ^ (-(4 / 3 : ℝ))) := by
        rw [Measure.volume_eq_prod, lintegral_prod _ (by fun_prop)]
    _ ≤ ∫⁻ q0, (closedBall (0 : ℂ) R).indicator
          (fun _ => M * (ENNReal.ofReal (C ^ 2 * R ^ (2 / 3 : ℝ)) * NNReal.pi)) q0 := by
        refine lintegral_mono fun q0 => ?_
        have hsplit : ∀ q1 : ℂ, S'.indicator (1 : ℂ × ℂ → ℝ≥0∞) (q0, q1) =
            (closedBall (0 : ℂ) R).indicator (1 : ℂ → ℝ≥0∞) q0 *
              (closedBall (0 : ℂ) (C * ‖q0‖)).indicator (1 : ℂ → ℝ≥0∞) q1 := by
          intro q1
          have hmem : (q0, q1) ∈ S' ↔
              q0 ∈ closedBall (0 : ℂ) R ∧ q1 ∈ closedBall (0 : ℂ) (C * ‖q0‖) := by
            rw [mem_closedBall_zero_iff, mem_closedBall_zero_iff]; exact Iff.rfl
          by_cases h1 : q0 ∈ closedBall (0 : ℂ) R
          · by_cases h2 : q1 ∈ closedBall (0 : ℂ) (C * ‖q0‖)
            · rw [indicator_of_mem (hmem.mpr ⟨h1, h2⟩), indicator_of_mem h1,
                indicator_of_mem h2]; simp
            · rw [indicator_of_notMem (fun h => h2 (hmem.mp h).2), indicator_of_notMem h2,
                mul_zero]
          · rw [indicator_of_notMem (fun h => h1 (hmem.mp h).1), indicator_of_notMem h1, zero_mul]
        simp_rw [hsplit]
        have hcomm : ∀ q1 : ℂ, (closedBall (0 : ℂ) R).indicator (1 : ℂ → ℝ≥0∞) q0 *
            (closedBall (0 : ℂ) (C * ‖q0‖)).indicator (1 : ℂ → ℝ≥0∞) q1 *
              (M * ‖q0‖ₑ ^ (-(4 / 3 : ℝ))) =
            ((closedBall (0 : ℂ) R).indicator (1 : ℂ → ℝ≥0∞) q0 * (M * ‖q0‖ₑ ^ (-(4 / 3 : ℝ)))) *
              (closedBall (0 : ℂ) (C * ‖q0‖)).indicator (1 : ℂ → ℝ≥0∞) q1 := fun q1 => by ring
        simp_rw [hcomm]
        rw [lintegral_const_mul _ (measurable_one.indicator measurableSet_closedBall),
          lintegral_indicator_one measurableSet_closedBall, Complex.volume_closedBall]
        by_cases h1 : q0 ∈ closedBall (0 : ℂ) R
        · rw [indicator_of_mem h1, indicator_of_mem h1, Pi.one_apply, one_mul]
          have hq : ‖q0‖ ≤ R := by rwa [mem_closedBall, dist_zero_right] at h1
          calc M * ‖q0‖ₑ ^ (-(4 / 3 : ℝ)) * (ENNReal.ofReal (C * ‖q0‖) ^ 2 * NNReal.pi)
              = M * ((‖q0‖ₑ ^ (-(4 / 3 : ℝ)) * ENNReal.ofReal (C * ‖q0‖) ^ 2) * NNReal.pi) := by
                ring
            _ ≤ M * (ENNReal.ofReal (C ^ 2 * R ^ (2 / 3 : ℝ)) * NNReal.pi) := by
                gcongr; exact enorm_rpow_mul_sq_le hC0.le hq
        · rw [indicator_of_notMem h1, indicator_of_notMem h1]; simp
    _ < ∞ := by
        rw [lintegral_indicator measurableSet_closedBall, setLIntegral_const]
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top hM (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ENNReal.coe_lt_top)) measure_closedBall_lt_top

/-! ### Moving into the chart -/

/-- The matrix of the substitution `P(s, t) ↦ P(l, m)` on moment coordinates. -/
def cubicMat (g : Form × Form) : Matrix (Fin 4) (Fin 4) ℂ :=
  let a := g.1.1; let b := g.1.2; let c := g.2.1; let d := g.2.2
  !![a ^ 3, 3 * a ^ 2 * c, 3 * a * c ^ 2, c ^ 3;
     a ^ 2 * b, 2 * a * b * c + a ^ 2 * d, b * c ^ 2 + 2 * a * c * d, c ^ 2 * d;
     a * b ^ 2, b ^ 2 * c + 2 * a * b * d, a * d ^ 2 + 2 * b * c * d, c * d ^ 2;
     b ^ 3, 3 * b ^ 2 * d, 3 * b * d ^ 2, d ^ 3]

/-- The substitution on cubics as a complex-linear map. -/
noncomputable def cubicActL (g : Form × Form) : Cubic →ₗ[ℂ] Cubic := Matrix.toLin' (cubicMat g)

/-- `cubicActL` is `cubicAct`. -/
theorem cubicActL_apply (g : Form × Form) (P : Cubic) : cubicActL g P = cubicAct g P := by
  ext i
  fin_cases i <;> simp [cubicActL, cubicMat, cubicAct, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_four] <;> ring

/-- `cubicAct g` is measurable. -/
theorem measurable_cubicAct (g : Form × Form) : Measurable (cubicAct g) := by
  have : cubicAct g = cubicActL g := funext fun P => (cubicActL_apply g P).symm
  rw [this]
  exact (LinearMap.continuous_of_finiteDimensional _).measurable

/-- `det_ℂ (P ↦ g · P) = det(g)⁶`. -/
theorem det_cubicActL (g : Form × Form) : (cubicActL g).det = det2 g ^ 6 := by
  rw [cubicActL, LinearMap.det_toLin', Matrix.det_succ_row_zero]
  simp [cubicMat, det2, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix,
    Fin.succAbove]
  ring

/-- A substitution with `|det g| = 1` preserves Lebesgue measure on cubic space. -/
theorem lintegral_comp_cubicAct {g : Form × Form} (hg : ‖det2 g‖ = 1) {F : Cubic → ℝ≥0∞}
    (hF : Measurable F) : ∫⁻ P, F (cubicAct g P) = ∫⁻ P, F P := by
  have hdet : (cubicActL g).det ≠ 0 := by
    rw [det_cubicActL]; exact pow_ne_zero 6 (norm_ne_zero_iff.mp (by rw [hg]; norm_num))
  have h := lintegral_comp_complexLinear volume (cubicActL g) hdet hF
  simp_rw [cubicActL_apply] at h
  rw [h, det_cubicActL, Complex.normSq_eq_norm_sq, norm_pow, hg]
  simp

/-- A substitution with `|det g| = 1` preserves `|𝔇|^{-4/3}`. -/
theorem twoCubeDensity_cubicAct_of_norm {g : Form × Form} (hg : ‖det2 g‖ = 1) (P : Cubic) :
    twoCubeDensity (cubicAct g P) = twoCubeDensity P := by
  rw [twoCubeDensity_cubicAct g (norm_ne_zero_iff.mp (by rw [hg]; norm_num)), ← ofReal_norm, hg]
  simp

/-- The four chart substitutions: the identity, `s ↔ t`, `t ↦ s + t`, `t ↦ -s + t`. -/
def chartPair : Fin 4 → Form × Form :=
  ![((1, 0), (0, 1)), ((0, 1), (1, 0)), ((1, 0), (1, 1)), ((1, 0), (-1, 1))]

/-- The chart substitutions have `|det| = 1`. -/
theorem norm_det2_chartPair (j : Fin 4) : ‖det2 (chartPair j)‖ = 1 := by
  fin_cases j <;> simp [chartPair, det2]

/-- **The covering inequality.** `‖P‖ ≤ max_j |(g_j · P)₀|`, i.e.
`‖P‖ ≤ max(|P(1,0)|, |P(0,1)|, |P(1,1)|, |P(1,-1)|)`. -/
theorem exists_chart (P : Cubic) : ∃ j : Fin 4, ‖P‖ ≤ ‖cubicAct (chartPair j) P 0‖ := by
  have e0 : cubicAct (chartPair 0) P 0 = P 0 := by simp [cubicAct, chartPair]
  have e1 : cubicAct (chartPair 1) P 0 = P 3 := by simp [cubicAct, chartPair]
  have e2 : cubicAct (chartPair 2) P 0 = P 0 + 3 * P 1 + 3 * P 2 + P 3 := by
    simp [cubicAct, chartPair]
  have e3 : cubicAct (chartPair 3) P 0 = P 0 - 3 * P 1 + 3 * P 2 - P 3 := by
    simp [cubicAct, chartPair]; ring
  obtain ⟨a, ha⟩ : ∃ a, a = P 0 + 3 * P 1 + 3 * P 2 + P 3 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = P 0 - 3 * P 1 + 3 * P 2 - P 3 := ⟨_, rfl⟩
  rw [← ha] at e2
  rw [← hb] at e3
  set m := max (max ‖P 0‖ ‖P 3‖) (max ‖a‖ ‖b‖)
  have h0 : ‖P 0‖ ≤ m := le_max_of_le_left (le_max_left _ _)
  have h3 : ‖P 3‖ ≤ m := le_max_of_le_left (le_max_right _ _)
  have h2 : ‖a‖ ≤ m := le_max_of_le_right (le_max_left _ _)
  have h4 : ‖b‖ ≤ m := le_max_of_le_right (le_max_right _ _)
  have hm0 : 0 ≤ m := (norm_nonneg _).trans h0
  have n6 : ‖(6 : ℂ)‖ = 6 := by norm_num
  have n2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have k1 : ‖P 1‖ ≤ m := by
    have : P 1 = (a - b - 2 * P 3) / 6 := by rw [ha, hb]; ring
    rw [this, norm_div, n6, div_le_iff₀ (by norm_num)]
    have e := norm_sub_le (a - b) (2 * P 3)
    have e' := norm_sub_le a b
    rw [norm_mul, n2] at e
    linarith
  have k2 : ‖P 2‖ ≤ m := by
    have : P 2 = (a + b - 2 * P 0) / 6 := by rw [ha, hb]; ring
    rw [this, norm_div, n6, div_le_iff₀ (by norm_num)]
    have e := norm_sub_le (a + b) (2 * P 0)
    have e' := norm_add_le a b
    rw [norm_mul, n2] at e
    linarith
  have hm : ‖P‖ ≤ m := by
    refine (pi_norm_le_iff_of_nonneg hm0).mpr fun i => ?_
    fin_cases i
    exacts [h0, k1, k2, h3]
  rcases max_choice (max ‖P 0‖ ‖P 3‖) (max ‖a‖ ‖b‖) with h | h <;>
    [rcases max_choice ‖P 0‖ ‖P 3‖ with h' | h'; rcases max_choice ‖a‖ ‖b‖ with h' | h']
  · exact ⟨0, by rw [e0]; exact hm.trans (le_of_eq (h.trans h'))⟩
  · exact ⟨1, by rw [e1]; exact hm.trans (le_of_eq (h.trans h'))⟩
  · exact ⟨2, by rw [e2]; exact hm.trans (le_of_eq (h.trans h'))⟩
  · exact ⟨3, by rw [e3]; exact hm.trans (le_of_eq (h.trans h'))⟩

/-- **`|𝔇|^{-4/3}` is integrable on balls.** -/
theorem lintegral_closedBall_twoCubeDensity_lt_top (R : ℝ) :
    ∫⁻ P in closedBall (0 : Cubic) R, twoCubeDensity P < ∞ := by
  set L : Fin 4 → Cubic →L[ℂ] Cubic := fun j =>
    LinearMap.toContinuousLinearMap (cubicActL (chartPair j))
  set C : Fin 4 → ℝ := fun j => ‖L j‖ + 1
  have hC : ∀ j, 1 ≤ C j := fun j => by simp only [C]; linarith [norm_nonneg (L j)]
  have hLP : ∀ j P, ‖cubicAct (chartPair j) P‖ ≤ (C j - 1) * ‖P‖ := fun j P => by
    change ‖cubicAct (chartPair j) P‖ ≤ (‖L j‖ + 1 - 1) * ‖P‖
    rw [add_sub_cancel_right]
    have := (L j).le_opNorm P
    simpa [L, cubicActL_apply] using this
  set G : Fin 4 → Cubic → ℝ≥0∞ := fun j => (chart (C j) (C j * R)).indicator twoCubeDensity
  have hG : ∀ j, Measurable (G j) := fun j =>
    measurable_twoCubeDensity.indicator (measurableSet_chart _ _)
  have hpt : ∀ P, (closedBall (0 : Cubic) R).indicator twoCubeDensity P ≤
      ∑ j, G j (cubicAct (chartPair j) P) := by
    intro P
    by_cases hP : P ∈ closedBall (0 : Cubic) R
    · rw [indicator_of_mem hP]
      obtain ⟨j, hj⟩ := exists_chart P
      refine le_trans ?_ (Finset.single_le_sum (fun j _ => zero_le) (Finset.mem_univ j))
      have hPR : ‖P‖ ≤ R := mem_closedBall_zero_iff.mp hP
      have hQ : cubicAct (chartPair j) P ∈ chart (C j) (C j * R) := by
        have h1 := hLP j P
        have hC1 := hC j
        refine ⟨?_, ?_⟩
        · nlinarith [norm_nonneg P]
        · nlinarith [norm_nonneg P]
      simp only [G]
      rw [indicator_of_mem hQ, twoCubeDensity_cubicAct_of_norm (norm_det2_chartPair j)]
    · rw [indicator_of_notMem hP]; exact zero_le
  rw [← lintegral_indicator measurableSet_closedBall]
  calc ∫⁻ P, (closedBall (0 : Cubic) R).indicator twoCubeDensity P
      ≤ ∫⁻ P, ∑ j, G j (cubicAct (chartPair j) P) := lintegral_mono hpt
    _ = ∑ j, ∫⁻ P, G j (cubicAct (chartPair j) P) :=
        lintegral_finsetSum _ fun j _ => (hG j).comp (measurable_cubicAct _)
    _ = ∑ j, ∫⁻ P, G j P := by
        congr 1; funext j; exact lintegral_comp_cubicAct (norm_det2_chartPair j) (hG j)
    _ < ∞ := ENNReal.sum_lt_top.mpr fun j _ => lintegral_chart_lt_top (hC j) _

/-! ### Local finiteness -/

/-- **The bounding density is dominated by `|𝔇|^{-4/3}` on balls**, for `0 ≤ β < 2`: both
exponents `1` and `1 + β/6` are at most `4/3`, and `‖P‖`, `‖H(P)‖`, `|𝔇(P)|` are bounded. -/
theorem densityBound_le_on_ball {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 2) (R : ℝ) :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ P ∈ closedBall (0 : Cubic) R,
      densityBound β P ≤ K * twoCubeDensity P := by
  obtain ⟨Md, hMd⟩ := (isCompact_closedBall (0 : Cubic) R).exists_bound_of_continuousOn
    (f := disc) (by unfold disc; fun_prop)
  obtain ⟨Mh, hMh⟩ := (isCompact_closedBall (0 : Cubic) R).exists_bound_of_continuousOn
    (f := hess) (by unfold hess; fun_prop)
  set M := max Md 0 + 1
  have hM : 1 ≤ M := by simp only [M]; linarith [le_max_right Md 0]
  set R' := max R 0
  set Mh' := max Mh 0
  set k1 := R' ^ (β / 3) * M ^ (1 / 3 : ℝ)
  set k2 := Mh' ^ (β / 2) * M ^ (1 / 3 - β / 6)
  have hk1 : 0 ≤ k1 := by positivity
  have hk2 : 0 ≤ k2 := by positivity
  refine ⟨ENNReal.ofReal (k1 + k2 + 1), ENNReal.ofReal_lt_top, fun P hP => ?_⟩
  by_cases hd : disc P = 0
  · have : twoCubeDensity P = ⊤ := by
      simp [twoCubeDensity, hd, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
    rw [this, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))]
    exact le_top
  have hdpos : 0 < ‖disc P‖ := norm_pos_iff.mpr hd
  have hdM : ‖disc P‖ ≤ M := by
    have := hMd P hP; simp only [M]; linarith [le_max_left Md 0]
  have hPR : ‖P‖ ≤ R' := (mem_closedBall_zero_iff.mp hP).trans (le_max_left _ _)
  have hHM : ‖hess P‖ ≤ Mh' := (hMh P hP).trans (le_max_left _ _)
  -- convert to real numbers
  have hinv : ∀ e : ℝ, ((‖disc P‖₊ : ℝ≥0∞)⁻¹) ^ e = ENNReal.ofReal (‖disc P‖ ^ (-e)) := by
    intro e; rw [inv_nnnorm_rpow, enorm_rpow_eq_ofReal hd]
  have hdb : densityBound β P = ENNReal.ofReal (‖P‖ ^ (β / 3) * ‖disc P‖ ^ (-(1 : ℝ)) +
      ‖hess P‖ ^ (β / 2) * ‖disc P‖ ^ (-(1 + β / 6))) := by
    rw [densityBound, hinv (1 + β / 6), ← ENNReal.rpow_one ((‖disc P‖₊ : ℝ≥0∞)⁻¹), hinv 1,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [hdb, twoCubeDensity, hinv, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set d := ‖disc P‖
  have e1 : d ^ (-(1 : ℝ)) = d ^ (1 / 3 : ℝ) * d ^ (-(4 / 3 : ℝ)) := by
    rw [← Real.rpow_add hdpos]; norm_num
  have e2 : d ^ (-(1 + β / 6)) = d ^ (1 / 3 - β / 6) * d ^ (-(4 / 3 : ℝ)) := by
    rw [← Real.rpow_add hdpos]; congr 1; ring
  have b1 : ‖P‖ ^ (β / 3) * d ^ (1 / 3 : ℝ) ≤ k1 := by
    change ‖P‖ ^ (β / 3) * d ^ (1 / 3 : ℝ) ≤ R' ^ (β / 3) * M ^ (1 / 3 : ℝ)
    gcongr
  have b2 : ‖hess P‖ ^ (β / 2) * d ^ (1 / 3 - β / 6) ≤ k2 := by
    have : 0 ≤ 1 / 3 - β / 6 := by linarith
    change ‖hess P‖ ^ (β / 2) * d ^ (1 / 3 - β / 6) ≤ Mh' ^ (β / 2) * M ^ (1 / 3 - β / 6)
    gcongr
  have hd43 : 0 ≤ d ^ (-(4 / 3 : ℝ)) := by positivity
  rw [e1, e2]
  nlinarith [mul_le_mul_of_nonneg_right b1 hd43, mul_le_mul_of_nonneg_right b2 hd43]

/-- **Interface, part 2, proved.** For `0 ≤ β < 2`, `rowMeasure β` is finite on closed balls. -/
theorem locallyFiniteRow {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 2) : LocallyFiniteRow β := by
  intro r
  obtain ⟨K, hK, hb⟩ := densityBound_le_on_ball hβ0 hβ r
  have hD := densityBound_holds hβ0 hβ
  calc rowMeasure β (closedBall 0 r)
      ≤ (ENNReal.ofReal (densityConst β) • (volume : Measure Cubic).withDensity
          (densityBound β)) (closedBall 0 r) := Measure.le_iff'.mp hD _
    _ = ENNReal.ofReal (densityConst β) * ∫⁻ P in closedBall (0 : Cubic) r, densityBound β P := by
        rw [Measure.smul_apply, withDensity_apply _ measurableSet_closedBall, smul_eq_mul]
    _ ≤ ENNReal.ofReal (densityConst β) *
          ∫⁻ P in closedBall (0 : Cubic) r, K * twoCubeDensity P := by
        gcongr 1
        exact setLIntegral_mono' measurableSet_closedBall hb
    _ = ENNReal.ofReal (densityConst β) *
          (K * ∫⁻ P in closedBall (0 : Cubic) r, twoCubeDensity P) := by
        rw [lintegral_const_mul _ measurable_twoCubeDensity]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.mul_lt_top hK (lintegral_closedBall_twoCubeDensity_lt_top r))

end SLT.PositionFour
