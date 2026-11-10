/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Toolkit.Quadratic
public import SLT.PositionFour.Upstream.Local

/-!
# Local integrability of `F` (note §2, Lemma "Weighted two-cube measure bound", second half)

* `lintegral_closedBall_discDensity_lt_top`: `∫_{‖P‖ ≤ R} |𝔇(P)|^{-t} dP < ∞` for `1 < t ≤ 3/2`;
* `locallyIntegrableF`: the interface statement `LocallyIntegrableF`.

The proof is the cone chart of `SLT.PositionFour.Upstream.Local` (there at `t = 4/3`), with the
exponent left free:

1. as a quadratic in `P₃`, `𝔇` has leading coefficient `P₀²` and discriminant
   `16 (P₁² - P₀P₂)³`, so the full-plane bound (`lintegral_quadratic_eq_rpow`) gives
   `∫ |𝔇|^{-t} dP₃ ≲ |P₀|^{2t-4} |P₁² - P₀P₂|^{-v}` with `v = 3t - 3` (`lintegral_last_le_rpow`);
2. the `P₂`-integral over `|P₂| ≤ C|P₀|` is `≲ |P₀|^{2-2v}` by the shifted disc at exponent
   `v ∈ (0, 2)` (`lintegral_middle_le_rpow`), and the `P₁`-integral over `|P₁| ≤ C|P₀|` gives
   `|P₀|²`; the result `|P₀|^{6-4t}` is bounded on `|P₀| ≤ R` because `6 - 4t ≥ 0`
   (`lintegral_chart_discDensity_lt_top`);
3. the four unimodular substitutions of `Upstream/Local.lean` (`chartPair`, `exists_chart`) move
   any cubic into the chart and preserve `𝔇` and Lebesgue measure.

Departure from the note: the note needs only `6 - 4t > -2` at the last step (integrability of
`|P₀|^{6-4t}` on a disc); we assume `t ≤ 3/2`, so that the last integrand is bounded, which
covers both exponents `4/3` and `11/8` that the note uses.
-/

@[expose] public section

namespace SLT.MiddlePositions

open MeasureTheory Set Metric SLT.PositionFour
open scoped ENNReal

/-! ### The density `|𝔇|^{-t}` -/

/-- `|𝔇(P)|^{-t}`, with value `∞` where `𝔇(P) = 0` (for `t > 0`). -/
noncomputable def discDensity (t : ℝ) (P : Cubic) : ℝ≥0∞ := ((‖disc P‖₊ : ℝ≥0∞)⁻¹) ^ t

/-- `|𝔇|^{-t}` is measurable. -/
@[fun_prop] theorem measurable_discDensity (t : ℝ) : Measurable (discDensity t) := by
  unfold discDensity disc; fun_prop

/-- `|𝔇|^{-4/3}` is the two-cube density. -/
theorem discDensity_four_thirds : discDensity (4 / 3) = twoCubeDensity := rfl

/-- A substitution with `|det g| = 1` preserves `|𝔇|^{-t}`. -/
theorem discDensity_cubicAct_of_norm {g : Form × Form} (hg : ‖det2 g‖ = 1) (t : ℝ) (P : Cubic) :
    discDensity t (cubicAct g P) = discDensity t P := by
  have h1 : ‖det2 g‖₊ = 1 := by ext; simpa using hg
  simp only [discDensity]
  rw [disc_cubicAct, nnnorm_mul, nnnorm_pow, h1, one_pow, one_mul]

/-! ### The last-coordinate integral -/

/-- The constant of `lintegral_last_le_rpow`. -/
noncomputable def lastConstT (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (4 ^ (t - 1) * 16 ^ (1 - t)) * quadConstT t + 1

/-- `lastConstT t < ∞` for `1 < t < 2`. -/
theorem lastConstT_lt_top {t : ℝ} (ht1 : 1 < t) (ht2 : t < 2) : lastConstT t < ∞ :=
  ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (quadConstT_lt_top ht1 ht2),
    ENNReal.one_lt_top⟩

/-- **The `P₃`-integral.** For `1 < t < 2`,
`∫ |𝔇(q₀, q₁, q₂, v)|^{-t} dv ≲ |q₀|^{-(4-2t)} |q₁² - q₀q₂|^{-(3t-3)}`. -/
theorem lintegral_last_le_rpow {t : ℝ} (ht1 : 1 < t) (ht2 : t < 2) (q0 q1 q2 : ℂ) :
    ∫⁻ v : ℂ, discDensity t ![q0, q1, q2, v] ≤
      lastConstT t * (‖q0‖ₑ ^ (-(4 - 2 * t)) * ‖q1 ^ 2 - q0 * q2‖ₑ ^ (-(3 * t - 3))) := by
  have hL : lastConstT t ≠ 0 := by simp [lastConstT]
  by_cases h0 : q0 = 0
  · rw [h0, enorm_zero_rpow_neg (by linarith), ENNReal.top_mul
      (enorm_rpow_neg_ne_zero _ (by linarith)), ENNReal.mul_top hL]
    exact le_top
  by_cases hX : q1 ^ 2 - q0 * q2 = 0
  · rw [hX, enorm_zero_rpow_neg (by linarith), ENNReal.mul_top
      (enorm_rpow_neg_ne_zero _ (by linarith)), ENNReal.mul_top hL]
    exact le_top
  have hA : q0 ^ 2 ≠ 0 := pow_ne_zero 2 h0
  have hΔ : (4 * q1 ^ 3 - 6 * q0 * q1 * q2) ^ 2 - 4 * q0 ^ 2 * (4 * q0 * q2 ^ 3 -
      3 * q1 ^ 2 * q2 ^ 2) ≠ 0 := by
    rw [discr_disc]; exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hX)
  have hq := lintegral_quadratic_eq_rpow hA hΔ t
  have hint : ∫⁻ v : ℂ, discDensity t ![q0, q1, q2, v] =
      ∫⁻ v : ℂ, ‖q0 ^ 2 * v ^ 2 + (4 * q1 ^ 3 - 6 * q0 * q1 * q2) * v +
        (4 * q0 * q2 ^ 3 - 3 * q1 ^ 2 * q2 ^ 2)‖ₑ ^ (-t) := by
    refine lintegral_congr fun v => ?_
    rw [discDensity, inv_nnnorm_rpow, disc_eq_quadratic]
    rfl
  rw [hint, hq, discr_disc]
  have h0n : 0 < ‖q0‖ := norm_pos_iff.mpr h0
  have hXn : 0 < ‖q1 ^ 2 - q0 * q2‖ := norm_pos_iff.mpr hX
  have e1 : ‖q0 ^ 2‖ ^ (t - 2) = ‖q0‖ ^ (-(4 - 2 * t)) := by
    rw [norm_pow, ← Real.rpow_natCast, ← Real.rpow_mul h0n.le]
    congr 1; push_cast; ring
  have e2 : ‖16 * (q1 ^ 2 - q0 * q2) ^ 3‖ ^ (1 - t) =
      16 ^ (1 - t) * ‖q1 ^ 2 - q0 * q2‖ ^ (-(3 * t - 3)) := by
    rw [norm_mul, norm_pow, Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_natCast ‖q1 ^ 2 - q0 * q2‖ 3, ← Real.rpow_mul hXn.le,
      show ((3 : ℕ) : ℝ) * (1 - t) = -(3 * t - 3) by push_cast; ring]
    norm_num
  have hreal : 4 ^ (t - 1) * ‖q0 ^ 2‖ ^ (t - 2) * ‖16 * (q1 ^ 2 - q0 * q2) ^ 3‖ ^ (1 - t) =
      (4 ^ (t - 1) * 16 ^ (1 - t)) *
        (‖q0‖ ^ (-(4 - 2 * t)) * ‖q1 ^ 2 - q0 * q2‖ ^ (-(3 * t - 3))) := by
    rw [e1, e2]; ring
  rw [hreal, ENNReal.ofReal_mul (p := 4 ^ (t - 1) * 16 ^ (1 - t)) (by positivity),
    ENNReal.ofReal_mul (p := ‖q0‖ ^ (-(4 - 2 * t))) (by positivity),
    ← enorm_rpow_eq_ofReal h0, ← enorm_rpow_eq_ofReal hX]
  calc ENNReal.ofReal (4 ^ (t - 1) * 16 ^ (1 - t)) *
        (‖q0‖ₑ ^ (-(4 - 2 * t)) * ‖q1 ^ 2 - q0 * q2‖ₑ ^ (-(3 * t - 3))) * quadConstT t
      = (ENNReal.ofReal (4 ^ (t - 1) * 16 ^ (1 - t)) * quadConstT t) *
        (‖q0‖ₑ ^ (-(4 - 2 * t)) * ‖q1 ^ 2 - q0 * q2‖ₑ ^ (-(3 * t - 3))) := by ring
    _ ≤ _ := by gcongr; exact le_self_add

/-! ### The middle-coordinate integral -/

/-- **The `P₂`-integral.** For `q₀ ≠ 0`, `C > 0` and `v > 0`,
`∫_{|q₂| ≤ C|q₀|} |q₁² - q₀ q₂|^{-v} dq₂ ≤ L_v C^{2-v} |q₀|^{2-2v}`. -/
theorem lintegral_middle_le_rpow {q0 : ℂ} (h0 : q0 ≠ 0) (q1 : ℂ) {C : ℝ} (hC : 0 < C) {v : ℝ}
    (hv : 0 < v) :
    ∫⁻ q2 in closedBall (0 : ℂ) (C * ‖q0‖), ‖q1 ^ 2 - q0 * q2‖ₑ ^ (-v) ≤
      discConstP v * ENNReal.ofReal (C ^ (2 - v) * ‖q0‖ ^ (2 - 2 * v)) := by
  have h0n : 0 < ‖q0‖ := norm_pos_iff.mpr h0
  have hfac : ∀ q2 : ℂ, ‖q1 ^ 2 - q0 * q2‖ₑ ^ (-v) =
      ‖q0‖ₑ ^ (-v) * ‖q2 - q1 ^ 2 / q0‖ₑ ^ (-v) := by
    intro q2
    rw [show q1 ^ 2 - q0 * q2 = -(q0 * (q2 - q1 ^ 2 / q0)) by field_simp; ring, enorm_neg,
      enorm_mul, ENNReal.mul_rpow_of_ne_top enorm_ne_top enorm_ne_top]
  simp_rw [hfac]
  rw [lintegral_const_mul _ (by fun_prop)]
  have hreal : ‖q0‖ ^ (-v) * (C * ‖q0‖) ^ (2 - v) = C ^ (2 - v) * ‖q0‖ ^ (2 - 2 * v) := by
    rw [Real.mul_rpow hC.le h0n.le, mul_left_comm, ← Real.rpow_add h0n]
    congr 2; ring
  calc ‖q0‖ₑ ^ (-v) * ∫⁻ q2 in closedBall (0 : ℂ) (C * ‖q0‖), ‖q2 - q1 ^ 2 / q0‖ₑ ^ (-v)
      ≤ ‖q0‖ₑ ^ (-v) * (discConstP v * ENNReal.ofReal ((C * ‖q0‖) ^ (2 - v))) := by
        gcongr; exact lintegral_closedBall_rpow_sub_le_rpow hv _ (by positivity)
    _ = discConstP v * ENNReal.ofReal (C ^ (2 - v) * ‖q0‖ ^ (2 - 2 * v)) := by
        rw [enorm_rpow_eq_ofReal h0, ← hreal, ENNReal.ofReal_mul (by positivity)]
        ring

/-- The `P₀`-integrand after the `P₁`-integral:
`|q₀|^{-(4-2t)} |q₀|^{2-2v} (C |q₀|)² ≤ C² R^{6-4t}` on `|q₀| ≤ R`, for `v = 3t - 3`, `t ≤ 3/2`. -/
theorem enorm_rpow_mul_ofReal_mul_sq_le {t : ℝ} (ht : t ≤ 3 / 2) {q0 : ℂ} {C R : ℝ}
    (hC : 0 ≤ C) (hq : ‖q0‖ ≤ R) :
    ‖q0‖ₑ ^ (-(4 - 2 * t)) * ENNReal.ofReal (‖q0‖ ^ (2 - 2 * (3 * t - 3))) *
        ENNReal.ofReal (C * ‖q0‖) ^ 2 ≤
      ENNReal.ofReal (C ^ 2 * R ^ (6 - 4 * t)) := by
  by_cases h0 : q0 = 0
  · simp [h0]
  have h0n : 0 < ‖q0‖ := norm_pos_iff.mpr h0
  rw [enorm_rpow_eq_ofReal h0, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : ‖q0‖ ^ (-(4 - 2 * t)) * ‖q0‖ ^ (2 - 2 * (3 * t - 3)) * (C * ‖q0‖) ^ 2 =
      C ^ 2 * ‖q0‖ ^ (6 - 4 * t) := by
    rw [← Real.rpow_add h0n, mul_pow, ← Real.rpow_natCast ‖q0‖ 2, mul_left_comm,
      ← Real.rpow_add h0n]
    congr 2; push_cast; ring
  rw [this]
  gcongr
  linarith

/-! ### The cone chart -/

/-- **The chart integral.** For `1 < t ≤ 3/2` and `C ≥ 1`,
`∫_{‖P‖ ≤ R, ‖P‖ ≤ C|P₀|} |𝔇(P)|^{-t} dP < ∞`. -/
theorem lintegral_chart_discDensity_lt_top {t : ℝ} (ht1 : 1 < t) (ht : t ≤ 3 / 2) {C : ℝ}
    (hC : 1 ≤ C) (R : ℝ) :
    ∫⁻ P, (chart C R).indicator (discDensity t) P < ∞ := by
  have hC0 : 0 < C := by linarith
  have ht2 : t < 2 := by linarith
  have hv : 0 < 3 * t - 3 := by linarith
  have hv2 : 3 * t - 3 < 2 := by linarith
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
  set M : ℝ≥0∞ := lastConstT t * (discConstP (3 * t - 3) * ENNReal.ofReal (C ^ (2 - (3 * t - 3))))
  have hM : M < ∞ :=
    ENNReal.mul_lt_top (lastConstT_lt_top ht1 ht2)
      (ENNReal.mul_lt_top (discConstP_lt_top hv2) ENNReal.ofReal_lt_top)
  set g : ℂ → ℝ≥0∞ := fun q0 =>
    ‖q0‖ₑ ^ (-(4 - 2 * t)) * ENNReal.ofReal (‖q0‖ ^ (2 - 2 * (3 * t - 3)))
  have hg : Measurable g := by fun_prop
  -- step a: the chart lies over `S`
  have hpt : ∀ P : Cubic, (chart C R).indicator (discDensity t) P ≤
      S.indicator 1 (cubicEquiv3 P).1 * discDensity t P := by
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
      S.indicator 1 p.1 * discDensity t (cubicEquiv3.symm p) :=
    ((measurable_one.indicator hS).comp measurable_fst).mul
      ((measurable_discDensity t).comp cubicEquiv3.symm.measurable)
  calc ∫⁻ P, (chart C R).indicator (discDensity t) P
      ≤ ∫⁻ P, S.indicator 1 (cubicEquiv3 P).1 *
          discDensity t (cubicEquiv3.symm (cubicEquiv3 P)) :=
        lintegral_mono fun P => by rw [cubicEquiv3.symm_apply_apply]; exact hpt P
    _ = ∫⁻ p, S.indicator 1 p.1 * discDensity t (cubicEquiv3.symm p) :=
        measurePreserving_cubicEquiv3.lintegral_comp_emb cubicEquiv3.measurableEmbedding
          (fun p => S.indicator 1 p.1 * discDensity t (cubicEquiv3.symm p))
    _ = ∫⁻ x, S.indicator 1 x * ∫⁻ v, discDensity t ![x.1.1, x.1.2, x.2, v] := by
        rw [Measure.volume_eq_prod, lintegral_prod _ hF.aemeasurable]
        refine lintegral_congr fun x => ?_
        change ∫⁻ v, S.indicator 1 x * discDensity t ![x.1.1, x.1.2, x.2, v] = _
        exact lintegral_const_mul _ (by fun_prop)
    _ ≤ ∫⁻ x, S.indicator 1 x * (lastConstT t * (‖x.1.1‖ₑ ^ (-(4 - 2 * t)) *
          ‖x.1.2 ^ 2 - x.1.1 * x.2‖ₑ ^ (-(3 * t - 3)))) := by
        gcongr with x; exact lintegral_last_le_rpow ht1 ht2 _ _ _
    _ = ∫⁻ y, ∫⁻ q2, S.indicator 1 (y, q2) * (lastConstT t * (‖y.1‖ₑ ^ (-(4 - 2 * t)) *
          ‖y.2 ^ 2 - y.1 * q2‖ₑ ^ (-(3 * t - 3)))) := by
        rw [Measure.volume_eq_prod, lintegral_prod _ (by fun_prop)]
    _ ≤ ∫⁻ y, S'.indicator 1 y * (M * g y.1) := by
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
            (lastConstT t * (‖y.1‖ₑ ^ (-(4 - 2 * t)) *
              ‖y.2 ^ 2 - y.1 * q2‖ₑ ^ (-(3 * t - 3)))) =
            (S'.indicator 1 y * lastConstT t * ‖y.1‖ₑ ^ (-(4 - 2 * t))) *
              (closedBall (0 : ℂ) (C * ‖y.1‖)).indicator
                (fun q2 => ‖y.2 ^ 2 - y.1 * q2‖ₑ ^ (-(3 * t - 3))) q2 := by
          intro q2
          by_cases h2 : q2 ∈ closedBall (0 : ℂ) (C * ‖y.1‖)
          · simp only [indicator_of_mem h2, Pi.one_apply]; ring
          · simp only [indicator_of_notMem h2, mul_zero, zero_mul]
        simp_rw [hrw]
        rw [lintegral_const_mul _ ((by fun_prop : Measurable fun q2 : ℂ =>
            ‖y.2 ^ 2 - y.1 * q2‖ₑ ^ (-(3 * t - 3))).indicator measurableSet_closedBall),
          lintegral_indicator measurableSet_closedBall]
        calc S'.indicator 1 y * lastConstT t * ‖y.1‖ₑ ^ (-(4 - 2 * t)) *
              ∫⁻ q2 in closedBall (0 : ℂ) (C * ‖y.1‖), ‖y.2 ^ 2 - y.1 * q2‖ₑ ^ (-(3 * t - 3))
            ≤ S'.indicator 1 y * lastConstT t * ‖y.1‖ₑ ^ (-(4 - 2 * t)) *
                (discConstP (3 * t - 3) * ENNReal.ofReal (C ^ (2 - (3 * t - 3)) *
                  ‖y.1‖ ^ (2 - 2 * (3 * t - 3)))) := by
              gcongr; exact lintegral_middle_le_rpow hy _ hC0 hv
          _ = S'.indicator 1 y * (M * g y.1) := by
              simp only [M, g]
              rw [ENNReal.ofReal_mul (by positivity)]
              ring
    _ = ∫⁻ q0, ∫⁻ q1, S'.indicator 1 (q0, q1) * (M * g q0) := by
        rw [Measure.volume_eq_prod, lintegral_prod _ (by fun_prop)]
    _ ≤ ∫⁻ q0, (closedBall (0 : ℂ) R).indicator
          (fun _ => M * (ENNReal.ofReal (C ^ 2 * R ^ (6 - 4 * t)) * NNReal.pi)) q0 := by
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
            (closedBall (0 : ℂ) (C * ‖q0‖)).indicator (1 : ℂ → ℝ≥0∞) q1 * (M * g q0) =
            ((closedBall (0 : ℂ) R).indicator (1 : ℂ → ℝ≥0∞) q0 * (M * g q0)) *
              (closedBall (0 : ℂ) (C * ‖q0‖)).indicator (1 : ℂ → ℝ≥0∞) q1 := fun q1 => by ring
        simp_rw [hcomm]
        rw [lintegral_const_mul _ (measurable_one.indicator measurableSet_closedBall),
          lintegral_indicator_one measurableSet_closedBall, Complex.volume_closedBall]
        by_cases h1 : q0 ∈ closedBall (0 : ℂ) R
        · rw [indicator_of_mem h1, indicator_of_mem h1, Pi.one_apply, one_mul]
          have hq : ‖q0‖ ≤ R := by rwa [mem_closedBall, dist_zero_right] at h1
          calc M * g q0 * (ENNReal.ofReal (C * ‖q0‖) ^ 2 * NNReal.pi)
              = M * ((g q0 * ENNReal.ofReal (C * ‖q0‖) ^ 2) * NNReal.pi) := by ring
            _ ≤ M * (ENNReal.ofReal (C ^ 2 * R ^ (6 - 4 * t)) * NNReal.pi) := by
                gcongr; exact enorm_rpow_mul_ofReal_mul_sq_le ht hC0.le hq
        · rw [indicator_of_notMem h1, indicator_of_notMem h1]; simp
    _ < ∞ := by
        rw [lintegral_indicator measurableSet_closedBall, setLIntegral_const]
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top hM (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ENNReal.coe_lt_top)) measure_closedBall_lt_top

/-! ### Balls -/

/-- **`|𝔇|^{-t}` is integrable on balls**, for `1 < t ≤ 3/2`. -/
theorem lintegral_closedBall_discDensity_lt_top {t : ℝ} (ht1 : 1 < t) (ht : t ≤ 3 / 2)
    (R : ℝ) : ∫⁻ P in closedBall (0 : Cubic) R, discDensity t P < ∞ := by
  set L : Fin 4 → Cubic →L[ℂ] Cubic := fun j =>
    LinearMap.toContinuousLinearMap (cubicActL (chartPair j))
  set C : Fin 4 → ℝ := fun j => ‖L j‖ + 1
  have hC : ∀ j, 1 ≤ C j := fun j => by simp only [C]; linarith [norm_nonneg (L j)]
  have hLP : ∀ j P, ‖cubicAct (chartPair j) P‖ ≤ (C j - 1) * ‖P‖ := fun j P => by
    change ‖cubicAct (chartPair j) P‖ ≤ (‖L j‖ + 1 - 1) * ‖P‖
    rw [add_sub_cancel_right]
    have := (L j).le_opNorm P
    simpa [L, cubicActL_apply] using this
  set G : Fin 4 → Cubic → ℝ≥0∞ := fun j => (chart (C j) (C j * R)).indicator (discDensity t)
  have hG : ∀ j, Measurable (G j) := fun j =>
    (measurable_discDensity t).indicator (measurableSet_chart _ _)
  have hpt : ∀ P, (closedBall (0 : Cubic) R).indicator (discDensity t) P ≤
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
      rw [indicator_of_mem hQ, discDensity_cubicAct_of_norm (norm_det2_chartPair j)]
    · rw [indicator_of_notMem hP]; exact zero_le
  rw [← lintegral_indicator measurableSet_closedBall]
  calc ∫⁻ P, (closedBall (0 : Cubic) R).indicator (discDensity t) P
      ≤ ∫⁻ P, ∑ j, G j (cubicAct (chartPair j) P) := lintegral_mono hpt
    _ = ∑ j, ∫⁻ P, G j (cubicAct (chartPair j) P) :=
        lintegral_finsetSum _ fun j _ => (hG j).comp (measurable_cubicAct _)
    _ = ∑ j, ∫⁻ P, G j P := by
        congr 1; funext j; exact lintegral_comp_cubicAct (norm_det2_chartPair j) (hG j)
    _ < ∞ := ENNReal.sum_lt_top.mpr fun j _ => lintegral_chart_discDensity_lt_top ht1 ht (hC j) _

/-! ### Local integrability of `F` -/

/-- `F = |𝔇|^{-4/3} + ‖P‖^{1/4} |𝔇|^{-11/8}`. -/
theorem F_eq (P : Cubic) :
    F P = twoCubeDensity P + ENNReal.ofReal (‖P‖ ^ (1 / 4 : ℝ)) * discDensity (11 / 8) P := rfl

/-- **Interface 2, proved.** `F` is integrable on every closed ball. -/
theorem locallyIntegrableF : LocallyIntegrableF := by
  intro r
  set r' := max r 0
  have hb : ∀ P ∈ closedBall (0 : Cubic) r,
      ENNReal.ofReal (‖P‖ ^ (1 / 4 : ℝ)) * discDensity (11 / 8) P ≤
        ENNReal.ofReal (r' ^ (1 / 4 : ℝ)) * discDensity (11 / 8) P := by
    intro P hP
    have hPr : ‖P‖ ≤ r' := (mem_closedBall_zero_iff.mp hP).trans (le_max_left _ _)
    gcongr
  simp_rw [F_eq]
  rw [lintegral_add_left measurable_twoCubeDensity]
  refine ENNReal.add_lt_top.mpr ⟨lintegral_closedBall_twoCubeDensity_lt_top r, ?_⟩
  calc ∫⁻ P in closedBall (0 : Cubic) r,
        ENNReal.ofReal (‖P‖ ^ (1 / 4 : ℝ)) * discDensity (11 / 8) P
      ≤ ∫⁻ P in closedBall (0 : Cubic) r,
          ENNReal.ofReal (r' ^ (1 / 4 : ℝ)) * discDensity (11 / 8) P :=
        setLIntegral_mono (by fun_prop) hb
    _ = ENNReal.ofReal (r' ^ (1 / 4 : ℝ)) *
          ∫⁻ P in closedBall (0 : Cubic) r, discDensity (11 / 8) P :=
        lintegral_const_mul _ (measurable_discDensity _)
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lintegral_closedBall_discDensity_lt_top (by norm_num) (by norm_num) r)

end SLT.MiddlePositions
