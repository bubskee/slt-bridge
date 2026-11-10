/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Upstream.Planar
public import SLT.PositionFour.Upstream.Coords
public import SLT.PositionFour.Upstream.RefFibre

/-!
# One-variable estimates for local finiteness

* `lintegral_quadratic_eq`: for a complex quadratic `A v² + B v + C` with `A ≠ 0` and
  `Δ = B² - 4AC ≠ 0`, `∫_ℂ |A v² + B v + C|^{-4/3} dv = 4^{1/3} K |A|^{-2/3} |Δ|^{-1/3}`, where
  `K = ∫_ℂ |z² - 1|^{-4/3} dz < ∞` (`lintegral_sq_sub_one_lt_top`). This is the note's
  "scaling the full plane" step, at the exponent `4/3`;
* `lintegral_closedBall_rpow_sub_le`: `∫_{|z| ≤ ρ} |z - w|^{-1} dz ≤ L ρ`, uniformly in `w`.
-/

@[expose] public section

namespace SLT.PositionFour

open MeasureTheory Set Metric
open scoped ENNReal

/-- The constant `K = ∫_ℂ |z² - 1|^{-4/3} dz`. -/
noncomputable def quadConst : ℝ≥0∞ := ∫⁻ z : ℂ, ‖z ^ 2 - 1‖ₑ ^ (-(4 / 3 : ℝ))

/-- `K < ∞`. -/
theorem quadConst_lt_top : quadConst < ∞ := by
  have h := lintegral_twoPoint_lt_top (a := 1) (b := -1) (by norm_num) (p := 4 / 3) (q := 4 / 3)
    (c := 0) (by norm_num) (by norm_num) le_rfl (by norm_num)
  refine lt_of_eq_of_lt (lintegral_congr fun z => ?_) h
  rw [show z ^ 2 - 1 = (z - 1) * (z - -1) by ring, enorm_mul,
    ENNReal.mul_rpow_of_ne_top enorm_ne_top enorm_ne_top]
  simp

/-- **The full-plane quadratic integral.** For `A ≠ 0` and `Δ = B² - 4AC ≠ 0`,
`∫ |A v² + B v + C|^{-4/3} dv = 4^{1/3} K |A|^{-2/3} |Δ|^{-1/3}`. -/
theorem lintegral_quadratic_eq {A B C : ℂ} (hA : A ≠ 0) (hΔ : B ^ 2 - 4 * A * C ≠ 0) :
    ∫⁻ v : ℂ, ‖A * v ^ 2 + B * v + C‖ₑ ^ (-(4 / 3 : ℝ)) =
      ENNReal.ofReal (4 ^ (1 / 3 : ℝ) * ‖A‖ ^ (-(2 / 3 : ℝ)) *
        ‖B ^ 2 - 4 * A * C‖ ^ (-(1 / 3 : ℝ))) * quadConst := by
  set Δ := B ^ 2 - 4 * A * C
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (Δ / (4 * A ^ 2)) two_pos
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hΔ
    have : Δ / (4 * A ^ 2) = 0 := by rw [← hd]; ring
    rwa [div_eq_zero_iff, or_iff_left (by simpa using hA)] at this
  set w₀ := B / (2 * A)
  set h : ℂ → ℝ≥0∞ := fun w => ‖A * d ^ 2 * ((w / d) ^ 2 - 1)‖ₑ ^ (-(4 / 3 : ℝ))
  have hh : Measurable h := by fun_prop
  have hshift : ∀ v : ℂ, A * v ^ 2 + B * v + C = A * d ^ 2 * (((v + w₀) / d) ^ 2 - 1) := by
    intro v
    simp only [w₀]
    field_simp
    rw [hd]
    field_simp
    ring
  have hscale : ∀ z : ℂ, h (d * z) = ‖A * d ^ 2‖ₑ ^ (-(4 / 3 : ℝ)) *
      ‖z ^ 2 - 1‖ₑ ^ (-(4 / 3 : ℝ)) := by
    intro z
    simp only [h]
    rw [mul_div_cancel_left₀ z hd0, enorm_mul, ENNReal.mul_rpow_of_ne_top enorm_ne_top enorm_ne_top]
  have hnd : ENNReal.ofReal (Complex.normSq d) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Complex.normSq_pos.mpr hd0)
  have hint : ∫⁻ w, h w = ENNReal.ofReal (Complex.normSq d) * ∫⁻ z, h (d * z) := by
    rw [lintegral_comp_mul_left hd0 hh, ← mul_assoc,
      ENNReal.mul_inv_cancel hnd ENNReal.ofReal_ne_top, one_mul]
  -- the real constant
  have ha : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hδ : 0 < ‖Δ‖ := norm_pos_iff.mpr hΔ
  have hdn : ‖d‖ ^ 2 = ‖Δ‖ / (4 * ‖A‖ ^ 2) := by
    rw [← norm_pow, hd, norm_div, norm_mul, norm_pow]; norm_num
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd0
  have hreal : ‖d‖ ^ 2 * (‖A‖ * ‖d‖ ^ 2) ^ (-(4 / 3 : ℝ)) =
      4 ^ (1 / 3 : ℝ) * ‖A‖ ^ (-(2 / 3 : ℝ)) * ‖Δ‖ ^ (-(1 / 3 : ℝ)) := by
    rw [hdn]
    set a := ‖A‖
    set δ := ‖Δ‖
    set t := δ / (4 * a ^ 2)
    have ht : 0 < t := by positivity
    have h4 : (0 : ℝ) < 4 * a ^ 2 := by positivity
    calc t * (a * t) ^ (-(4 / 3 : ℝ))
        = a ^ (-(4 / 3 : ℝ)) * (t ^ (1 : ℝ) * t ^ (-(4 / 3 : ℝ))) := by
          rw [Real.mul_rpow ha.le ht.le, Real.rpow_one]; ring
      _ = a ^ (-(4 / 3 : ℝ)) * t ^ (-(1 / 3 : ℝ)) := by rw [← Real.rpow_add ht]; norm_num
      _ = a ^ (-(4 / 3 : ℝ)) * (δ ^ (-(1 / 3 : ℝ)) * (4 * a ^ 2) ^ (1 / 3 : ℝ)) := by
          rw [Real.div_rpow hδ.le h4.le, Real.rpow_neg h4.le, div_inv_eq_mul]
      _ = a ^ (-(4 / 3 : ℝ)) * (δ ^ (-(1 / 3 : ℝ)) * (4 ^ (1 / 3 : ℝ) * a ^ (2 / 3 : ℝ))) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast a 2,
            ← Real.rpow_mul ha.le]
          norm_num
      _ = 4 ^ (1 / 3 : ℝ) * (a ^ (-(4 / 3 : ℝ)) * a ^ (2 / 3 : ℝ)) * δ ^ (-(1 / 3 : ℝ)) := by ring
      _ = 4 ^ (1 / 3 : ℝ) * a ^ (-(2 / 3 : ℝ)) * δ ^ (-(1 / 3 : ℝ)) := by
          rw [← Real.rpow_add ha]; norm_num
  calc ∫⁻ v : ℂ, ‖A * v ^ 2 + B * v + C‖ₑ ^ (-(4 / 3 : ℝ)) = ∫⁻ v, h (v + w₀) := by
        simp_rw [hshift]; rfl
    _ = ∫⁻ w, h w := lintegral_add_right_eq_self h w₀
    _ = ENNReal.ofReal (Complex.normSq d) * (‖A * d ^ 2‖ₑ ^ (-(4 / 3 : ℝ)) * quadConst) := by
        rw [hint]; simp_rw [hscale]; rw [lintegral_const_mul _ (by fun_prop)]; rfl
    _ = _ := by
        rw [← mul_assoc]
        congr 1
        rw [← hreal, Complex.normSq_eq_norm_sq, ← ofReal_norm (A * d ^ 2),
          ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr (mul_ne_zero hA (pow_ne_zero 2 hd0))),
          ← ENNReal.ofReal_mul (by positivity),
          norm_mul, norm_pow]

/-- The constant `L = ∫_{|z| < 1} |z|^{-1} + vol(closedBall 0 1)` of the shifted-disc bound. -/
noncomputable def discConst : ℝ≥0∞ :=
  (∫⁻ z in ball (0 : ℂ) 1, ‖z‖ₑ ^ (-(1 : ℝ))) + volume (closedBall (0 : ℂ) 1)

/-- `L < ∞`. -/
theorem discConst_lt_top : discConst < ∞ :=
  ENNReal.add_lt_top.mpr
    ⟨lintegral_ball_rpow_neg_lt_top (p := 1) (by norm_num) 1, measure_closedBall_lt_top⟩

/-- `∫_{|z| ≤ 1} |z - w|^{-1} dz ≤ L` for every `w`. -/
theorem lintegral_closedBall_one_rpow_sub_le (w : ℂ) :
    ∫⁻ z in closedBall (0 : ℂ) 1, ‖z - w‖ₑ ^ (-(1 : ℝ)) ≤ discConst := by
  have hpt : ∀ z : ℂ, (closedBall (0 : ℂ) 1).indicator (fun z => ‖z - w‖ₑ ^ (-(1 : ℝ))) z ≤
      (ball w 1).indicator (fun z => ‖z - w‖ₑ ^ (-(1 : ℝ))) z +
        (closedBall (0 : ℂ) 1).indicator 1 z := by
    intro z
    by_cases hz : z ∈ closedBall (0 : ℂ) 1
    · rw [indicator_of_mem hz, indicator_of_mem hz, Pi.one_apply]
      by_cases hzw : z ∈ ball w 1
      · rw [indicator_of_mem hzw]; exact le_self_add
      · rw [indicator_of_notMem hzw, zero_add]
        refine ENNReal.rpow_le_one_of_one_le_of_neg ?_ (by norm_num)
        rw [mem_ball, dist_eq_norm, not_lt] at hzw
        rw [← ofReal_norm, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hzw
    · rw [indicator_of_notMem hz]; exact zero_le
  rw [← lintegral_indicator measurableSet_closedBall]
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_left ((by fun_prop : Measurable fun z : ℂ => ‖z - w‖ₑ ^ (-(1 : ℝ))).indicator
    measurableSet_ball), lintegral_indicator_one measurableSet_closedBall, discConst]
  refine add_le_add ?_ le_rfl
  rw [lintegral_indicator measurableSet_ball]
  have := lintegral_sub_right_eq_self (μ := (volume : Measure ℂ))
    ((ball (0 : ℂ) 1).indicator fun z : ℂ => ‖z‖ₑ ^ (-(1 : ℝ))) w
  rw [lintegral_indicator measurableSet_ball] at this
  rw [← this, ← lintegral_indicator measurableSet_ball]
  refine le_of_eq (lintegral_congr fun z => ?_)
  simp only [indicator, mem_ball, dist_eq_norm, sub_zero]

/-- **The shifted disc.** `∫_{|z| ≤ ρ} |z - w|^{-1} dz ≤ L ρ` for every `w` and `ρ > 0`. -/
theorem lintegral_closedBall_rpow_sub_le (w : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ z in closedBall (0 : ℂ) ρ, ‖z - w‖ₑ ^ (-(1 : ℝ)) ≤ discConst * ENNReal.ofReal ρ := by
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  set F : ℂ → ℝ≥0∞ := (closedBall (0 : ℂ) ρ).indicator fun z => ‖z - w‖ₑ ^ (-(1 : ℝ))
  have hF : Measurable F := (by fun_prop : Measurable fun z : ℂ => ‖z - w‖ₑ ^ (-(1 : ℝ))).indicator
    measurableSet_closedBall
  have hnρ : Complex.normSq (ρ : ℂ) = ρ ^ 2 := by rw [Complex.normSq_ofReal]; ring
  have hscale := lintegral_comp_mul_left hρc hF
  have hFρ : ∀ y : ℂ, F (ρ * y) = ENNReal.ofReal ρ⁻¹ *
      (closedBall (0 : ℂ) 1).indicator (fun y => ‖y - w / ρ‖ₑ ^ (-(1 : ℝ))) y := by
    intro y
    have hmem : ρ * y ∈ closedBall (0 : ℂ) ρ ↔ y ∈ closedBall (0 : ℂ) 1 := by
      simp only [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hρ.le]
      constructor
      · intro h; nlinarith [norm_nonneg y]
      · intro h; nlinarith [norm_nonneg y]
    simp only [F]
    by_cases hy : y ∈ closedBall (0 : ℂ) 1
    · rw [indicator_of_mem (hmem.mpr hy), indicator_of_mem hy]
      have : ρ * y - w = ρ * (y - w / ρ) := by field_simp
      rw [this, enorm_mul, ENNReal.mul_rpow_of_ne_top enorm_ne_top enorm_ne_top]
      congr 1
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hρ.le,
        ENNReal.ofReal_rpow_of_pos hρ, Real.rpow_neg_one]
    · rw [indicator_of_notMem (fun h => hy (hmem.mp h)), indicator_of_notMem hy, mul_zero]
  have hint : ∫⁻ z, F z = ENNReal.ofReal (ρ ^ 2) * ∫⁻ y, F (ρ * y) := by
    rw [hscale, hnρ, ← mul_assoc, ENNReal.mul_inv_cancel
      (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top, one_mul]
  rw [← lintegral_indicator measurableSet_closedBall]
  change ∫⁻ z, F z ≤ _
  rw [hint]
  simp_rw [hFρ]
  rw [lintegral_const_mul _ ((by fun_prop : Measurable fun y : ℂ =>
      ‖y - w / ρ‖ₑ ^ (-(1 : ℝ))).indicator measurableSet_closedBall),
    lintegral_indicator measurableSet_closedBall]
  calc ENNReal.ofReal (ρ ^ 2) * (ENNReal.ofReal ρ⁻¹ *
        ∫⁻ y in closedBall (0 : ℂ) 1, ‖y - w / ρ‖ₑ ^ (-(1 : ℝ)))
      ≤ ENNReal.ofReal (ρ ^ 2) * (ENNReal.ofReal ρ⁻¹ * discConst) := by
        gcongr; exact lintegral_closedBall_one_rpow_sub_le _
    _ = discConst * ENNReal.ofReal ρ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_comm]
        congr 2; field_simp

end SLT.PositionFour
