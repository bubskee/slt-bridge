/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Downstream.Radial
public import SLT.PositionFour.Downstream.Quadratic
public import SLT.PositionFour.Downstream.Marginal
public import SLT.PositionFour.Downstream.LemmaOne
public import SLT.PositionFour.Downstream.Finiteness
public import SLT.PositionFour.Downstream.Shell

/-!
# The complex position-four threshold: the downstream half

Sections 2 and 3 of `complex_position_four.tex` (2026-11-09), assuming the density interface of
`SLT.PositionFour.Defs` (`DensityBound`, `LocallyFiniteRow`; the note's Section 1) as hypotheses.

* `SLT.PositionFour.Downstream.lemma_one`: Lemma 1, `∫_{‖λ‖ > 1} m_β(λ)^p < ∞` for
  `0 ≤ β < 2`, `p > 10/(6-β)`. Proved outright (no hypotheses on the density).
* `SLT.PositionFour.Downstream.sublevel_weighted_lt_top`: Section 3,
  `∫_{‖R‖ < 1} (W_β(w₁) + W_β(w₂)) < ∞`; `volume_sublevel_lt_top`: the endpoint.
* `SLT.PositionFour.Downstream.shell_lintegral_lt_top`, `integrableOn_shell`,
  `shell_lintegral_lt_top_of_interface`: `‖R‖^{-2s}` is integrable on the shell
  `{1/2 ≤ ‖w‖ < 1}` for every `s < 13/3`.

Module map: `Radial` (radial integrals on `ℂ`), `Quadratic` (inverse powers of a quadratic on a
disc), `Marginal` (the transverse marginal and its pointwise bounds), `LemmaOne`, `Finiteness`
(Section 3), `Shell` (the stretch). Notes: `SLT/PositionFour/NOTES_downstream.md`.
-/
