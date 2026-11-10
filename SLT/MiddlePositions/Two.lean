/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Two.Planar
public import SLT.MiddlePositions.Two.Kernel
public import SLT.MiddlePositions.Two.Suffix
public import SLT.MiddlePositions.Two.Prefix
public import SLT.MiddlePositions.Two.Assembly

/-!
# The complex margin at position two

Theorem "Position two" of `forum/complex_middle_positions/complex_middle_positions.tex`
(2026-11-09), from the interface of `SLT.MiddlePositions.Defs`:

* `SLT.MiddlePositions.Two.sublevelTwo`: `∫_{‖R₂ w‖ < 1} ‖w‖^{1/4} dw < ∞` on
  `Row2 × Row2 ≃ ℂ¹²`, assuming `WeightedTwoCubeBound C` and `FullPlaneQuadratic t K` for every
  `1 < t < 2` (only `t = 9/8, 4/3, 11/8` are used). `LocallyIntegrableF` is not used.
* `SLT.MiddlePositions.Two.sublevel_two_le`: the explicit bound
  `∫_{‖R₂‖ < 1} ‖w‖^{1/4} ≤ (C Msuf)² ∫∫ V 𝟙_{preSet}`.

Module map: `Planar` (shifted discs, tails, the note's `eq:quad0` and `eq:quadw`), `Kernel` (the
disc integral `L_t` and the `J` bounds), `Suffix` (the free-`q₀` integration and the suffix
kernel on unit `Q`-discs), `Prefix` (finiteness of the weighted prefix volume), `Assembly` (the
weight, the sublevel set, the interface and Tonelli). Notes: `SLT/MiddlePositions/NOTES_two.md`.
Audit: the root `Audit.lean`.
-/

@[expose] public section

namespace SLT.MiddlePositions.Two

open MeasureTheory SLT.PositionFour
open scoped ENNReal

/-- **Theorem (position two)** of `complex_middle_positions.tex`, from the interface:
`∫_{‖R₂ w‖ < 1} ‖w‖^{1/4} dw < ∞` on `Row2 × Row2 ≃ ℂ¹²`. Only `WeightedTwoCubeBound` and
`FullPlaneQuadratic` at `t = 9/8, 4/3, 11/8` are used; `LocallyIntegrableF` is not needed. -/
theorem sublevelTwo {C : ℝ} (hW : WeightedTwoCubeBound C)
    (hQ : ∀ t : ℝ, 1 < t → t < 2 → ∃ K, FullPlaneQuadratic t K) : SublevelTwo := by
  obtain ⟨K₀, hK₀⟩ := hQ (9 / 8) (by norm_num) (by norm_num)
  obtain ⟨K₁, hK₁⟩ := hQ (4 / 3) (by norm_num) (by norm_num)
  obtain ⟨K₂, hK₂⟩ := hQ (11 / 8) (by norm_num) (by norm_num)
  refine (sublevel_two_le hW (fullPlaneQuadratic_mono hK₀ (le_max_left K₀ 0))
    (fullPlaneQuadratic_mono hK₁ (le_max_left K₁ 0))
    (fullPlaneQuadratic_mono hK₂ (le_max_left K₂ 0)) (le_max_right _ _) (le_max_right _ _)
    (le_max_right _ _)).trans_lt ?_
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)) lintegral_pre_lt_top


end SLT.MiddlePositions.Two
