/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Toolkit.Quadratic
public import SLT.MiddlePositions.Toolkit.Weighted
public import SLT.MiddlePositions.Toolkit.Local
public import SLT.MiddlePositions.Toolkit.Shell

/-!
# The middle-position toolkit: the three interface statements of `Defs.lean`

Root import for `SLT.MiddlePositions.Toolkit.*`. Source: the note
`complex_middle_positions.tex` (2026-11-09), §2 and §6. All three interface statements are proved
with no hypotheses:

* `toolkit_weightedTwoCubeBound`: `∃ C, WeightedTwoCubeBound C` (with `C = 16/9`);
* `toolkit_locallyIntegrableF`: `LocallyIntegrableF`;
* `toolkit_fullPlaneQuadratic`: `∀ t ∈ (1, 2), ∃ C, FullPlaneQuadratic t C`
  (with `C = 4^{t-1} (K_t + 1)`, `K_t = ∫ |z² - 1|^{-t}`).

The shell corollary (note §6) for both middle positions, from the headline statements:

* `shell_two`: `SublevelTwo → ∀ s < 97/24, ∫_{shell} ‖R₂‖^{-2s} < ∞`;
* `shell_three`: `SublevelThree → ∀ s < 97/24, ∫_{shell} ‖R₃‖^{-2s} < ∞`.

Where each part of the note lives:

* Lemma "Planar powers and quadratics", last display: `fullPlaneQuadratic_quadC` (`Quadratic`),
  from `SLT.Pushforward.lintegral_quadratic_eq_rpow`; shifted disc:
  `SLT.Pushforward.lintegral_closedBall_rpow_sub_le_rpow`;
* Lemma "Weighted two-cube measure bound", first half: `W2_le_of_det2_ne_zero`,
  `twoCubeWeight_mul_le`, `lintegral_W2_twoCube_le`, `weightedTwoCubeBound_sixteen_ninths`
  (`Weighted`);
* the same lemma, second half: `locallyIntegrableF` (`Local`), from the cone chart of
  `SLT/PositionFour/Upstream/Local.lean` at a general exponent (`lintegral_last_le_rpow`,
  `lintegral_middle_le_rpow`, `lintegral_chart_discDensity_lt_top`,
  `lintegral_closedBall_discDensity_lt_top`, namespace `SLT.PositionFour`);
* §6 "A shell corollary without polar coordinates": `shell_two`, `shell_three` (`Shell`), from
  the general `SLT.Pushforward.lintegral_homShell_lt_top_of_moment`.
-/

@[expose] public section

namespace SLT.MiddlePositions

/-- **Interface 1.** The pushforward of `W₂ · Lebesgue` under the two-cube map is at most a
constant times `F · Lebesgue`. -/
theorem toolkit_weightedTwoCubeBound : ∃ C, WeightedTwoCubeBound C := weightedTwoCubeBound

/-- **Interface 2.** `F` is integrable on every closed ball. -/
theorem toolkit_locallyIntegrableF : LocallyIntegrableF := locallyIntegrableF

/-- **Interface 3.** For every `1 < t < 2` the full-plane quadratic bound holds with some
constant. -/
theorem toolkit_fullPlaneQuadratic : ∀ t : ℝ, 1 < t → t < 2 → ∃ C, FullPlaneQuadratic t C :=
  fullPlaneQuadratic

end SLT.MiddlePositions
