/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Upstream
public import SLT.PositionFour.Downstream

/-!
# The complex position-four threshold, unconditionally

The join of the two halves of `complex_position_four.tex` (2026-11-09). `Upstream` proves the
density interface of `Defs.lean` for every `0 ≤ β < 2` (the note's Section 1). `Downstream` derives
the finiteness statements from that interface (Sections 2 and 3). Here the two are composed, so
no hypothesis on the density remains.

`leadingMap` is the leading map `R = (λ₁ - λ₂, y₁, y₂)` at position four, on
`Row × Row ≃ ℂ¹²`. All norms are sup norms.

* `volume_sublevel_lt_top`: `Leb {‖R‖ < 1} < ∞`.
* `sublevel_weighted_lt_top`: `∫_{‖R‖ < 1} (W_β(w₁) + W_β(w₂)) < ∞` for `0 ≤ β < 2`.
* `shell_lintegral_lt_top`, `integrableOn_shell`: `‖R‖^{-2s}` is integrable on the shell
  `{1/2 ≤ ‖w‖ < 1}` for every `s < 13/3`.

Not formalised: the Euclidean-sphere form of the last statement, divergence at `s = 13/3` (the
note's Section 4), and any link to the stability and transfer steps of the paper.
-/

@[expose] public section

namespace SLT.PositionFour

open MeasureTheory
open scoped ENNReal

/-- **The density interface holds.** For `0 ≤ β < 2` the weighted row pushforward is dominated by
a constant times the bounding density, and is finite on closed balls. -/
theorem interface (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 2) :
    ∃ C, DensityBound β C ∧ LocallyFiniteRow β :=
  ⟨_, densityBound_holds hβ0 hβ, locallyFiniteRow hβ0 hβ⟩

/-- **The weighted unit sublevel volume is finite** (the note's Section 3), for `0 ≤ β < 2`. -/
theorem sublevel_weighted_lt_top {β : ℝ} (hβ0 : 0 ≤ β) (hβ2 : β < 2) :
    ∫⁻ w in {w : Row × Row | ‖leadingMap w‖ < 1},
      ENNReal.ofReal (rowWeight β w.1 + rowWeight β w.2) < ∞ :=
  Downstream.sublevel_weighted_lt_top hβ0 hβ2
    (densityBound_holds le_rfl (by norm_num)) (densityBound_holds hβ0 hβ2)
    (locallyFiniteRow le_rfl (by norm_num)) (locallyFiniteRow hβ0 hβ2)

/-- **The unit sublevel set of the leading map has finite volume.** -/
theorem volume_sublevel_lt_top : volume {w : Row × Row | ‖leadingMap w‖ < 1} < ∞ :=
  Downstream.volume_sublevel_lt_top
    (densityBound_holds le_rfl (by norm_num)) (locallyFiniteRow le_rfl (by norm_num))

/-- **The angular margin.** For every `s < 13/3`, `‖R‖^{-2s}` has finite integral over the shell
`{1/2 ≤ ‖w‖ < 1}`. The integrand is `∞` on the zero set of `R` when `s > 0`. -/
theorem shell_lintegral_lt_top {s : ℝ} (hs : s < 13 / 3) :
    ∫⁻ w in Downstream.rowShell, ‖leadingMap w‖ₑ⁻¹ ^ (2 * s) < ∞ :=
  Downstream.shell_lintegral_lt_top_of_interface hs interface

/-- **The angular margin, as integrability of a real function.** For every `s < 13/3`,
`w ↦ ‖R(w)‖^{-2s}` is integrable on the shell `{1/2 ≤ ‖w‖ < 1}`. -/
theorem integrableOn_shell {s : ℝ} (hs : s < 13 / 3) :
    IntegrableOn (fun w => ‖leadingMap w‖ ^ (-(2 * s))) Downstream.rowShell := by
  set β := max 0 ((6 * s - 22) / 2) with hβ
  have hβ0 : 0 ≤ β := le_max_left _ _
  have hβ2 : β < 2 := max_lt (by norm_num) (by linarith)
  have hsβ : 2 * s < 8 + β / 3 := by
    rcases le_total 0 ((6 * s - 22) / 2) with h' | h'
    · rw [hβ, max_eq_right h']; linarith
    · rw [hβ, max_eq_left h']; linarith
  exact Downstream.integrableOn_shell hβ0 hβ2 hsβ
    (densityBound_holds le_rfl (by norm_num)) (densityBound_holds hβ0 hβ2)
    (locallyFiniteRow le_rfl (by norm_num)) (locallyFiniteRow hβ0 hβ2)

end SLT.PositionFour
