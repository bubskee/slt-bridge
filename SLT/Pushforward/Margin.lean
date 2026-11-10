/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Threshold
public import SLT.MiddlePositions.Threshold

/-!
# The strict shell margin, for the three leading maps

* `StrictShellMargin R`: for a map `R` on a normed space `E` with Lebesgue measure, there is
  `s > 4` with `∫_{1/2 ≤ ‖w‖ < 1} ‖R w‖^{-2s} dw < ∞` (in `ℝ≥0∞`, so the integrand is `∞` on the
  zero set of `R`). The shell is `homShell E`, the sup-norm shell of the space.
* `strictShellMargin_leadingMaps`: the predicate holds for `leadingMap` (position four), `R2` and
  `R3` (positions two and three), as defined in `SLT/PositionFour/Defs.lean` and
  `SLT/MiddlePositions/Defs.lean`. It is a corollary of the headline theorems
  `SLT.PositionFour.shell_lintegral_lt_top` (`s < 13/3`) and
  `SLT.MiddlePositions.shellTwo_lintegral_lt_top`, `shellThree_lintegral_lt_top` (`s < 97/24`).
* `norm_leadingMap_eq_generators`: `leadingMap` is the `generators` family of the middle positions
  with zero suffix cubics, up to reindexing and zero components: the two have the same sup norm.

Lean does not prove that these maps are the leading part of the network error.
-/

@[expose] public section

namespace SLT.Pushforward

open MeasureTheory SLT.PositionFour SLT.MiddlePositions
open scoped ENNReal

/-- **The strict shell margin** of a map `R` on a normed space `E`: for some `s > 4`,
`‖R w‖^{-2s}` has finite integral over the shell `{1/2 ≤ ‖w‖ < 1}` (Lebesgue measure; the
integrand is `∞` on the zero set of `R`). -/
def StrictShellMargin {E V : Type*} [NormedAddCommGroup E] [MeasureSpace E]
    [NormedAddCommGroup V] (R : E → V) : Prop :=
  ∃ s : ℝ, 4 < s ∧ ∫⁻ w in homShell E, ‖R w‖ₑ⁻¹ ^ (2 * s) < ∞

/-- **The strict shell margin holds for the three leading maps**: `leadingMap` (position four),
`R2` and `R3` (positions two and three), as defined in the two `Defs.lean` files. -/
theorem strictShellMargin_leadingMaps :
    StrictShellMargin leadingMap ∧ StrictShellMargin R2 ∧ StrictShellMargin R3 :=
  ⟨⟨17 / 4, by norm_num, PositionFour.shell_lintegral_lt_top (by norm_num)⟩,
    ⟨193 / 48, by norm_num, shellTwo_lintegral_lt_top (by norm_num)⟩,
    ⟨193 / 48, by norm_num, shellThree_lintegral_lt_top (by norm_num)⟩⟩

/-- **`leadingMap` is the `generators` family with zero suffix cubics**, up to reindexing and zero
components: with `p₁, p₂` the row cubics of the two rows, `‖leadingMap w‖ = ‖generators p₁ 0 p₂ 0‖`
(sup norms). -/
theorem norm_leadingMap_eq_generators (w : Row × Row) :
    ‖leadingMap w‖ = ‖generators (rowCubic w.1) 0 (rowCubic w.2) 0‖ := by
  set g := generators (rowCubic w.1) 0 (rowCubic w.2) 0
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg g)).mpr fun i => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg (leadingMap w))).mpr fun i => ?_)
  · fin_cases i
    · exact norm_le_pi_norm g 10 |>.trans_eq' (by simp [g, generators, leadingMap])
    · exact norm_le_pi_norm g 8 |>.trans_eq' (by simp [g, generators, leadingMap])
    · exact norm_le_pi_norm g 0 |>.trans_eq' (by simp [g, generators, leadingMap])
    · exact norm_le_pi_norm g 1 |>.trans_eq' (by simp [g, generators, leadingMap])
    · exact norm_le_pi_norm g 4 |>.trans_eq' (by simp [g, generators, leadingMap])
    · exact norm_le_pi_norm g 5 |>.trans_eq' (by simp [g, generators, leadingMap])
  · fin_cases i
    · exact norm_le_pi_norm (leadingMap w) 2 |>.trans_eq' (by simp [g, generators, leadingMap])
    · exact norm_le_pi_norm (leadingMap w) 3 |>.trans_eq' (by simp [g, generators, leadingMap])
    · simp [g, generators]
    · simp [g, generators]
    · exact norm_le_pi_norm (leadingMap w) 4 |>.trans_eq' (by simp [g, generators, leadingMap])
    · exact norm_le_pi_norm (leadingMap w) 5 |>.trans_eq' (by simp [g, generators, leadingMap])
    · simp [g, generators]
    · simp [g, generators]
    · exact norm_le_pi_norm (leadingMap w) 1 |>.trans_eq' (by simp [g, generators, leadingMap])
    · simp [g, generators]
    · exact norm_le_pi_norm (leadingMap w) 0 |>.trans_eq' (by simp [g, generators, leadingMap])

end SLT.Pushforward
