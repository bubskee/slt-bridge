/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Upstream.Planar

/-!
# The reference integral (note §1, step 1)

With `w_β(z) = |z (1 - z)|^{-4/3} (1 + |z|)^{β/3}` on `ℂ` and `0 ≤ β < 2`,
`∬ w_β(x) w_β(y) |x - y|^{-2/3} dA(x) dA(y) < ∞` (`lintegral_refBilinear_lt_top`).

The note uses `w_β ∈ L¹ ∩ L^{4/3}` and Young's inequality for `|x - y| < 1` with
`K = 1_{|z|<1} |z|^{-2/3} ∈ L²`. Here Young is replaced by the pointwise inequality
`A B k ≤ (A B)^{4/3} + (A^{4/3} + B^{4/3}) k²` (`mul_mul_le_amgm`), which after Tonelli and
translation invariance needs exactly the same three facts:
* `lintegral_refWeight_lt_top`: `w_β ∈ L¹` (this is where `β < 2` enters);
* `lintegral_refWeight_rpow_lt_top`: `w_β ∈ L^{4/3}`;
* `lintegral_refKernel_sq_lt_top`: `K ∈ L²`.
-/

@[expose] public section

namespace SLT.PositionFour

open MeasureTheory Set Metric
open scoped ENNReal

/-- The note's reference weight `w_β(z) = |z|^{-4/3} |1 - z|^{-4/3} (1 + |z|)^{β/3}`. -/
noncomputable def refWeight (β : ℝ) (z : ℂ) : ℝ≥0∞ :=
  ‖z‖ₑ ^ (-(4 / 3 : ℝ)) * ‖1 - z‖ₑ ^ (-(4 / 3 : ℝ)) * ENNReal.ofReal ((1 + ‖z‖) ^ (β / 3))

/-- The local kernel `K(z) = 1_{|z| < 1} |z|^{-2/3}`. -/
noncomputable def refKernel (z : ℂ) : ℝ≥0∞ :=
  (ball (0 : ℂ) 1).indicator (fun z => ‖z‖ₑ ^ (-(2 / 3 : ℝ))) z

/-- `K` is even. -/
theorem refKernel_neg (z : ℂ) : refKernel (-z) = refKernel z := by
  simp [refKernel, indicator, mem_ball]

/-- `w_β` is measurable. -/
@[fun_prop] theorem measurable_refWeight (β : ℝ) : Measurable (refWeight β) := by
  unfold refWeight; fun_prop

/-- `K` is measurable. -/
@[fun_prop] theorem measurable_refKernel : Measurable refKernel :=
  (by fun_prop : Measurable fun z : ℂ => ‖z‖ₑ ^ (-(2 / 3 : ℝ))).indicator measurableSet_ball

/-- `‖1 - z‖ₑ = ‖z - 1‖ₑ`. -/
theorem enorm_one_sub (z : ℂ) : ‖1 - z‖ₑ = ‖z - 1‖ₑ := by rw [← enorm_neg, neg_sub]

/-- `w_β ∈ L¹` for `β < 2`. -/
theorem lintegral_refWeight_lt_top {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 2) :
    ∫⁻ z, refWeight β z < ∞ := by
  have h := lintegral_twoPoint_lt_top (a := 0) (b := 1) zero_ne_one (p := 4 / 3) (q := 4 / 3)
    (c := β / 3) (by norm_num) (by norm_num) (by positivity) (by linarith)
  simpa [refWeight, enorm_one_sub] using h

/-- `w_β ∈ L^{4/3}` for `0 ≤ β < 2`. -/
theorem lintegral_refWeight_rpow_lt_top {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 2) :
    ∫⁻ z, refWeight β z ^ (4 / 3 : ℝ) < ∞ := by
  have h := lintegral_twoPoint_lt_top (a := 0) (b := 1) zero_ne_one (p := 16 / 9) (q := 16 / 9)
    (c := 4 * β / 9) (by norm_num) (by norm_num) (by positivity) (by linarith)
  refine lt_of_eq_of_lt (lintegral_congr fun z => ?_) h
  rw [refWeight, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.rpow_mul (by positivity),
    enorm_one_sub, sub_zero]
  norm_num
  ring_nf

/-- `K ∈ L²`. -/
theorem lintegral_refKernel_sq_lt_top : ∫⁻ z, refKernel z ^ 2 < ∞ := by
  have h := lintegral_ball_rpow_neg_lt_top (p := 4 / 3) (by norm_num) 1
  refine lt_of_eq_of_lt ?_ h
  rw [← lintegral_indicator measurableSet_ball]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ ball (0 : ℂ) 1
  · simp only [refKernel, indicator_of_mem hz]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  · simp [refKernel, indicator_of_notMem hz]

/-- `x y ≤ x² + y²` in `ℝ≥0∞`. -/
theorem mul_le_sq_add_sq (x y : ℝ≥0∞) : x * y ≤ x ^ 2 + y ^ 2 := by
  rcases le_total x y with h | h
  · calc x * y ≤ y * y := mul_le_mul_left h y
      _ = y ^ 2 := (sq y).symm
      _ ≤ x ^ 2 + y ^ 2 := le_add_self
  · calc x * y ≤ x * x := mul_le_mul_right h x
      _ = x ^ 2 := (sq x).symm
      _ ≤ x ^ 2 + y ^ 2 := le_self_add

/-- The pointwise replacement for Young: `A B k ≤ (A B)^{4/3} + (A^{4/3} + B^{4/3}) k²`. -/
theorem mul_mul_le_amgm (A B k : ℝ≥0∞) :
    A * B * k ≤ (A * B) ^ (4 / 3 : ℝ) + (A ^ (4 / 3 : ℝ) + B ^ (4 / 3 : ℝ)) * k ^ 2 := by
  set X := (A * B) ^ (1 / 3 : ℝ)
  have hsplit : A * B = (A * B) ^ (2 / 3 : ℝ) * X := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num
  rcases le_total k X with hk | hk
  · -- `A B k ≤ A B X = (A B)^{4/3}`
    have : A * B * X = (A * B) ^ (4 / 3 : ℝ) := by
      rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num,
        ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num), ENNReal.rpow_one]
    calc A * B * k ≤ A * B * X := by gcongr
      _ = _ := this
      _ ≤ _ := le_self_add
  · -- `A B k = (A B)^{2/3} X k ≤ (A B)^{2/3} k²` and `(A B)^{2/3} ≤ A^{4/3} + B^{4/3}`
    have h23 : (A * B) ^ (2 / 3 : ℝ) ≤ A ^ (4 / 3 : ℝ) + B ^ (4 / 3 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      refine (mul_le_sq_add_sq _ _).trans_eq ?_
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num
    calc A * B * k = ((A * B) ^ (2 / 3 : ℝ) * X) * k := by rw [← hsplit]
      _ = (A * B) ^ (2 / 3 : ℝ) * (X * k) := mul_assoc _ _ _
      _ ≤ (A * B) ^ (2 / 3 : ℝ) * (k * k) := by gcongr
      _ = (A * B) ^ (2 / 3 : ℝ) * k ^ 2 := by rw [sq]
      _ ≤ (A ^ (4 / 3 : ℝ) + B ^ (4 / 3 : ℝ)) * k ^ 2 := by gcongr
      _ ≤ _ := le_add_self

/-- `|z|^{-2/3} ≤ 1 + K(z)`. -/
theorem enorm_rpow_le_one_add_refKernel (z : ℂ) : ‖z‖ₑ ^ (-(2 / 3 : ℝ)) ≤ 1 + refKernel z := by
  by_cases hz : z ∈ ball (0 : ℂ) 1
  · simp only [refKernel, indicator_of_mem hz]; exact le_add_self
  · simp only [refKernel, indicator_of_notMem hz, add_zero]
    refine ENNReal.rpow_le_one_of_one_le_of_neg ?_ (by norm_num)
    rw [mem_ball, dist_zero_right, not_lt] at hz
    rw [← ofReal_norm, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hz

/-- **The reference integral.** For `0 ≤ β < 2`,
`∬ w_β(x) w_β(y) |x - y|^{-2/3} dA(x) dA(y) < ∞`. -/
theorem lintegral_refBilinear_lt_top {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 2) :
    ∫⁻ x, ∫⁻ y, refWeight β x * refWeight β y * ‖x - y‖ₑ ^ (-(2 / 3 : ℝ)) < ∞ := by
  set w := refWeight β
  have hw : Measurable w := measurable_refWeight β
  have I1 := lintegral_refWeight_lt_top hβ0 hβ
  have I43 := lintegral_refWeight_rpow_lt_top hβ0 hβ
  have IK := lintegral_refKernel_sq_lt_top
  -- translation invariance of the kernel integral
  have hKx : ∀ x : ℂ, ∫⁻ y, refKernel (x - y) ^ 2 = ∫⁻ z, refKernel z ^ 2 := fun x => by
    simp_rw [← refKernel_neg (x - _), neg_sub]
    exact lintegral_sub_right_eq_self (fun z => refKernel z ^ 2) x
  have hKy : ∀ y : ℂ, ∫⁻ x, refKernel (x - y) ^ 2 = ∫⁻ z, refKernel z ^ 2 := fun y =>
    lintegral_sub_right_eq_self (fun z => refKernel z ^ 2) y
  -- the pointwise bound
  have hpt : ∀ x y : ℂ, w x * w y * ‖x - y‖ₑ ^ (-(2 / 3 : ℝ)) ≤
      w x * w y + (w x ^ (4 / 3 : ℝ) * w y ^ (4 / 3 : ℝ) +
        (w x ^ (4 / 3 : ℝ) * refKernel (x - y) ^ 2 +
          w y ^ (4 / 3 : ℝ) * refKernel (x - y) ^ 2)) := by
    intro x y
    calc w x * w y * ‖x - y‖ₑ ^ (-(2 / 3 : ℝ)) ≤ w x * w y * (1 + refKernel (x - y)) := by
          gcongr; exact enorm_rpow_le_one_add_refKernel _
      _ = w x * w y + w x * w y * refKernel (x - y) := by rw [mul_add, mul_one]
      _ ≤ _ := by
          gcongr
          refine (mul_mul_le_amgm _ _ _).trans_eq ?_
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), add_mul]
  have m43 : Measurable fun x => w x ^ (4 / 3 : ℝ) := hw.pow_const _
  have hmK : Measurable fun p : ℂ × ℂ => refKernel (p.1 - p.2) ^ 2 := by fun_prop
  -- the four pieces, on the product space
  set a : ℂ × ℂ → ℝ≥0∞ := fun p => w p.1 * w p.2
  set b : ℂ × ℂ → ℝ≥0∞ := fun p => w p.1 ^ (4 / 3 : ℝ) * w p.2 ^ (4 / 3 : ℝ)
  set c : ℂ × ℂ → ℝ≥0∞ := fun p => w p.1 ^ (4 / 3 : ℝ) * refKernel (p.1 - p.2) ^ 2
  set d : ℂ × ℂ → ℝ≥0∞ := fun p => w p.2 ^ (4 / 3 : ℝ) * refKernel (p.1 - p.2) ^ 2
  have ma : Measurable a := (hw.comp measurable_fst).mul (hw.comp measurable_snd)
  have mb : Measurable b := (m43.comp measurable_fst).mul (m43.comp measurable_snd)
  have mc : Measurable c := (m43.comp measurable_fst).mul hmK
  have md : Measurable d := (m43.comp measurable_snd).mul hmK
  have Ta : ∫⁻ p, a p ∂(volume.prod volume) < ∞ := by
    rw [lintegral_prod _ ma.aemeasurable, lintegral_lintegral_mul hw.aemeasurable hw.aemeasurable]
    exact ENNReal.mul_lt_top I1 I1
  have Tb : ∫⁻ p, b p ∂(volume.prod volume) < ∞ := by
    rw [lintegral_prod _ mb.aemeasurable,
      lintegral_lintegral_mul m43.aemeasurable m43.aemeasurable]
    exact ENNReal.mul_lt_top I43 I43
  have Tc : ∫⁻ p, c p ∂(volume.prod volume) < ∞ := by
    rw [lintegral_prod _ mc.aemeasurable]
    have : ∀ x, ∫⁻ y, c (x, y) = w x ^ (4 / 3 : ℝ) * ∫⁻ z, refKernel z ^ 2 := fun x => by
      change ∫⁻ y, w x ^ (4 / 3 : ℝ) * refKernel (x - y) ^ 2 = _
      rw [lintegral_const_mul _ (by fun_prop), hKx]
    simp_rw [this]
    rw [lintegral_mul_const _ m43]
    exact ENNReal.mul_lt_top I43 IK
  have Td : ∫⁻ p, d p ∂(volume.prod volume) < ∞ := by
    rw [lintegral_prod_symm _ md.aemeasurable]
    have : ∀ y, ∫⁻ x, d (x, y) = w y ^ (4 / 3 : ℝ) * ∫⁻ z, refKernel z ^ 2 := fun y => by
      change ∫⁻ x, w y ^ (4 / 3 : ℝ) * refKernel (x - y) ^ 2 = _
      rw [lintegral_const_mul _ (by fun_prop), hKy]
    simp_rw [this]
    rw [lintegral_mul_const _ m43]
    exact ENNReal.mul_lt_top I43 IK
  have hF : Measurable fun p : ℂ × ℂ => w p.1 * w p.2 * ‖p.1 - p.2‖ₑ ^ (-(2 / 3 : ℝ)) := by
    fun_prop
  calc ∫⁻ x, ∫⁻ y, w x * w y * ‖x - y‖ₑ ^ (-(2 / 3 : ℝ))
      = ∫⁻ p, w p.1 * w p.2 * ‖p.1 - p.2‖ₑ ^ (-(2 / 3 : ℝ)) ∂(volume.prod volume) :=
        (lintegral_prod _ hF.aemeasurable).symm
    _ ≤ ∫⁻ p, a p + (b p + (c p + d p)) ∂(volume.prod volume) :=
        lintegral_mono fun p => hpt p.1 p.2
    _ = ∫⁻ p, a p ∂(volume.prod volume) + (∫⁻ p, b p ∂(volume.prod volume) +
          (∫⁻ p, c p ∂(volume.prod volume) + ∫⁻ p, d p ∂(volume.prod volume))) := by
        rw [lintegral_add_left ma, lintegral_add_left mb, lintegral_add_left mc]
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨Ta, ENNReal.add_lt_top.mpr ⟨Tb,
        ENNReal.add_lt_top.mpr ⟨Tc, Td⟩⟩⟩

end SLT.PositionFour
