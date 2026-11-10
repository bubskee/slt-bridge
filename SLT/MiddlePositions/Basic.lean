/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Defs

/-!
# The middle positions: basic facts about the definitions

Facts about `F`, `W2`, `R2` and `R3` of `Defs.lean` that the toolkit and both position proofs use:
measurability of the bounding density, the lower bound `1 ≤ W₂`, and continuity of the two leading
maps.
-/

@[expose] public section

namespace SLT.MiddlePositions

open MeasureTheory SLT.PositionFour
open scoped ENNReal NNReal

/-- The bounding density `F` is measurable. -/
theorem measurable_F : Measurable F := by
  have hc : Continuous disc := by unfold disc; fun_prop
  have hd : Measurable fun P : Cubic => ((‖disc P‖₊ : ℝ≥0∞)⁻¹) ^ (11 / 8 : ℝ) :=
    (hc.measurable.nnnorm.coe_nnreal_ennreal.inv.pow_const _)
  unfold F
  exact measurable_twoCubeDensity.add ((measurable_norm.pow_const _).ennreal_ofReal.mul hd)

/-- `W₂ ≥ 1`. -/
theorem one_le_W2 (g : Form × Form) : 1 ≤ W2 g := by
  unfold W2
  have := Real.rpow_nonneg (norm_nonneg g.1.1) (1 / 4 : ℝ)
  have := Real.rpow_nonneg (norm_nonneg g.1.2) (1 / 4 : ℝ)
  have := Real.rpow_nonneg (norm_nonneg g.2.1) (1 / 4 : ℝ)
  have := Real.rpow_nonneg (norm_nonneg g.2.2) (1 / 4 : ℝ)
  linarith

/-- `R₂` is continuous. -/
theorem continuous_R2 : Continuous R2 := by
  unfold R2 generators twoCube cube
  fun_prop

/-- `R₃` is continuous. -/
theorem continuous_R3 : Continuous R3 := by
  unfold R3 generators twoCube cube
  fun_prop

end SLT.MiddlePositions
