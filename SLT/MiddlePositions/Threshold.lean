/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Toolkit
public import SLT.MiddlePositions.Two
public import SLT.MiddlePositions.Three

/-!
# The complex margin at the middle positions, unconditionally

The join of the three branches that formalize `complex_middle_positions.tex` (2026-11-09).
`Toolkit` proves the interface of `Defs.lean`. `Two` and `Three` derive the two headline
statements from that interface. Here they are composed, so no hypothesis remains.

`R2` and `R3` are the leading maps of the inactive entries at positions two and three, on
`ℂ¹²`, with the eleven generators of `Defs.lean`. All norms are sup norms.

* `sublevelTwo`, `sublevelThree`: `∫_{‖R_j w‖ < 1} ‖w‖^{1/4} dw < ∞`.
* `shellTwo_lintegral_lt_top`, `shellThree_lintegral_lt_top`: `‖R_j‖^{-2s}` is integrable on the
  shell `{1/2 ≤ ‖w‖ < 1}` for every `s < 97/24`. Since `97/24 > 4`, this is a strict margin.

Not formalised: the Euclidean-sphere form, any sharp threshold, and the link to the stability and
transfer steps of the paper.
-/

@[expose] public section

namespace SLT.MiddlePositions

open MeasureTheory
open scoped ENNReal

/-- **Position two.** `∫_{‖R₂ w‖ < 1} ‖w‖^{1/4} dw < ∞` over `ℂ¹²`. -/
theorem sublevelTwo : SublevelTwo := by
  obtain ⟨C, hC⟩ := toolkit_weightedTwoCubeBound
  exact Two.sublevelTwo hC toolkit_fullPlaneQuadratic

/-- **Position three.** `∫_{‖R₃ w‖ < 1} ‖w‖^{1/4} dw < ∞` over `ℂ¹²`. -/
theorem sublevelThree : SublevelThree := by
  obtain ⟨C, hC⟩ := toolkit_weightedTwoCubeBound
  exact Three.sublevelThree hC toolkit_locallyIntegrableF toolkit_fullPlaneQuadratic

/-- **The margin at position two.** For every `s < 97/24`, `‖R₂‖^{-2s}` has finite integral over
the shell `{1/2 ≤ ‖w‖ < 1}`. The integrand is `∞` on the zero set of `R₂` when `s > 0`. -/
theorem shellTwo_lintegral_lt_top {s : ℝ} (hs : s < 97 / 24) :
    ∫⁻ w in homShell (Row2 × Row2), ‖R2 w‖ₑ⁻¹ ^ (2 * s) < ∞ :=
  toolkit_shell_two sublevelTwo hs

/-- **The margin at position three.** For every `s < 97/24`, `‖R₃‖^{-2s}` has finite integral
over the shell `{1/2 ≤ ‖w‖ < 1}`. -/
theorem shellThree_lintegral_lt_top {s : ℝ} (hs : s < 97 / 24) :
    ∫⁻ w in homShell (Row3 × Row3), ‖R3 w‖ₑ⁻¹ ^ (2 * s) < ∞ :=
  toolkit_shell_three sublevelThree hs

end SLT.MiddlePositions
