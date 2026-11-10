# Complex integrability margins: index after the consolidation

This index covers `SLT/PositionFour`, `SLT/MiddlePositions` and the shared directory
`SLT/Pushforward`. The five session notes are kept as historical records:
`SLT/PositionFour/NOTES_upstream.md`, `SLT/PositionFour/NOTES_downstream.md`,
`SLT/MiddlePositions/NOTES_toolkit.md`, `SLT/MiddlePositions/NOTES_two.md` and
`SLT/MiddlePositions/NOTES_three.md`. Their audit commands, some file paths and some declaration
names are out of date. This file says where things live now. The last section lists every
declaration that was removed or renamed.

Every statement is about the leading maps as defined in `SLT/PositionFour/Defs.lean`
(`leadingMap`) and `SLT/MiddlePositions/Defs.lean` (`R2`, `R3`, `generators`). Lean does not prove
that these maps are the leading part of the network error.

Audit: every public declaration has a line in the root `Audit.lean`, checked by
`scripts/check_audit.sh`. The per-directory audit files are gone.

## Shared directory `SLT/Pushforward` (namespace `SLT.Pushforward`)

| File | Content |
|---|---|
| `Basic` | inverse powers in `ℝ≥0∞`: `enorm_inv_rpow_of_ne_zero`, `enorm_mul_inv_rpow`, `ofReal_rpow_neg_le`, … |
| `Linear` | complex-linear changes of variables: `det_restrictScalars_complex`, `lintegral_comp_complexLinear`, `lintegral_comp_mul_left` |
| `Planar` | planar power singularities: `lintegral_ball_rpow_neg_lt_top`, `lintegral_one_add_rpow_neg_lt_top`, `lintegral_twoPoint_lt_top` |
| `Radial` | disc areas, polar coordinates, centred and off-centre disc integrals, tails: `lintegral_ball_inv_rpow`, `lintegral_ball_sub_inv_rpow_le`, `setLIntegral_ball_inv_rpow_le`, `lintegral_norm_gt_inv_rpow`, `lintegral_max_one_rpow_neg_lt_top` |
| `Quadratic` | the full-plane quadratic integral at any exponent, `lintegral_quadratic_eq_rpow` (`K_t = quadConstT t`); the shifted closed disc, `lintegral_closedBall_rpow_sub_le_rpow` |
| `QuadraticDisc` | inverse powers of a quadratic on a disc: `lintegral_ball_inv_quadratic_le` (two roots), `lintegral_ball_one_inv_quadratic_le` (one dominant root) |
| `Shell` | the shell bound for a continuous cubically homogeneous map: `homShell`, `lintegral_homShell_lt_top_of_moment` and its dimension-24 form |
| `Margin` | the predicate `StrictShellMargin` and `strictShellMargin_leadingMaps` for all three maps; `norm_leadingMap_eq_generators` |

## `complex_position_four.tex`

| Step of the note | Lean now |
|---|---|
| §1 step 1, the reference integral | `PositionFour/Upstream/Reference.lean`, using `Pushforward/Planar` |
| §1 step 2, the reference fibre `ρ_β(P*) < ∞` | `Upstream/RefFibre.lean` (`refFibre_lt_top`), using `Pushforward/Linear` |
| §1 step 3, the two-cube pushforward | `Upstream/TwoCube.lean` (`twoCubeBound`), with `Sylvester`, `Area`, `Coords` |
| §1 step 4, transport and equation (2) | `Upstream/Density.lean` (`densityBound_holds`) |
| §1 step 5, local finiteness | `Upstream/Local.lean`: `lintegral_closedBall_discDensity_lt_top` (`|𝔇|^{-t}` on balls, `1 < t ≤ 3/2`), its case `t = 4/3` `lintegral_closedBall_twoCubeDensity_lt_top`, then `locallyFiniteRow`. Uses `Pushforward/Quadratic` |
| §1, the interface | `PositionFour/Threshold.lean` (`interface`); `Upstream.lean` (`upstream_densityBound`, `upstream_locallyFiniteRow`) |
| §2, Lemma 1 | `Downstream/Marginal.lean`, `Downstream/LemmaOne.lean` (`lemma_one`), using `Pushforward/Radial` and `Pushforward/QuadraticDisc` |
| §3, sublevel volume | `Downstream/Finiteness.lean`; unconditional forms in `Threshold.lean` (`volume_sublevel_lt_top`, `sublevel_weighted_lt_top`) |
| shell form, `s < 13/3` | `Pushforward/Shell.lean` (general lemma); `Downstream/Shell.lean` (the case `R = leadingMap`, `rowShell` = `homShell (Row × Row)`); `Threshold.lean` (`shell_lintegral_lt_top`, `integrableOn_shell`) |

## `complex_middle_positions.tex`

| Step of the note | Lean now |
|---|---|
| §2, Lemma "Planar powers and quadratics": full-plane quadratic | `Pushforward/Quadratic.lean` (`lintegral_quadratic_eq_rpow`); Interface 3 in `MiddlePositions/Toolkit/Quadratic.lean` (`fullPlaneQuadratic_quadC`, `fullPlaneQuadratic`, `fullPlaneQuadratic_mono`) |
| same lemma, item 1 (discs, tails) | `Pushforward/Quadratic.lean` (shifted closed disc), `Pushforward/Radial.lean` (off-centre open disc, tails) |
| same lemma, `eq:quad0`, `eq:quadw` | `MiddlePositions/Two/Planar.lean` (`lintegral_inv_quadratic_le`, `lintegral_rpow_mul_inv_quadratic_le`) |
| §2, Lemma "Weighted two-cube measure bound", first half | `Toolkit/Weighted.lean` |
| same lemma, second half (`F ∈ L¹_loc`) | the cone chart at general `t` in `PositionFour/Upstream/Local.lean`; `Toolkit/Local.lean` (`locallyIntegrableF`) |
| position two | `MiddlePositions/Two/` (`Kernel`, `Prefix`, `Suffix`, `Assembly`), `Two.lean` |
| position three | `MiddlePositions/Three/` (`Marginal`, `Prefix`, `Suffix`, `Assembly`), `Three.lean` |
| §6, shell corollary | `Pushforward/Shell.lean` (general lemma); `Toolkit/Shell.lean` (`shell_two`, `shell_three`); `Threshold.lean` (`shellTwo_lintegral_lt_top`, `shellThree_lintegral_lt_top`) |
| all three maps at once | `Pushforward/Margin.lean` (`strictShellMargin_leadingMaps`) |

## Removed or renamed declarations

Moves to another namespace, same statement (the replacement is the same proof, moved):

| Old | New |
|---|---|
| `SLT.MiddlePositions.homShell`, `measurableSet_homShell`, `homLayer`, `measurableSet_homLayer`, `homLayer_volume_le`, `lintegral_homShell_lt_top_of_moment`, `lintegral_homShell_lt_top_of_moment_24` | same names in `SLT.Pushforward` |
| `SLT.PositionFour.Downstream.enorm_inv_rpow_of_ne_zero`, `enorm_mul_inv_rpow`, `enorm_pow_inv_rpow`, `ofReal_inv_rpow_of_pos`, `ofReal_rpow_mul_inv_rpow_le`, `ofReal_rpow_neg_le` | same names in `SLT.Pushforward` (`Basic`) |
| `SLT.PositionFour.Downstream.lintegral_norm_comp`, `lintegral_ball_inv_rpow`, `lintegral_ball_sub_inv_rpow_le`, `lintegral_norm_gt_inv_rpow` | same names in `SLT.Pushforward` (`Radial`) |
| `SLT.PositionFour.Downstream.lintegral_ball_inv_mul_rpow_le`, `exists_quadratic_factor`, `lintegral_ball_inv_quadratic_le`, `exists_root_lower_bound`, `lintegral_ball_one_inv_quadratic_le` | same names in `SLT.Pushforward` (`QuadraticDisc`) |
| `SLT.PositionFour.det_restrictScalars_complex`, `lintegral_comp_complexLinear`, `lintegral_comp_mul_left` | same names in `SLT.Pushforward` (`Linear`) |
| `SLT.PositionFour.enorm_rpow_eq_ofReal`, `integrableOn_ball_rpow_neg`, `lintegral_ball_rpow_neg_lt_top`, `lintegral_one_add_rpow_neg_lt_top`, `integrable_indicator_ball_rpow_neg`, `lintegral_twoPoint_lt_top` | same names in `SLT.Pushforward` (`Planar`) |
| `SLT.MiddlePositions.quadConstT`, `quadConstT_lt_top`, `lintegral_quadratic_eq_rpow`, `discConstP`, `discConstP_lt_top`, `lintegral_closedBall_one_rpow_sub_le_rpow`, `lintegral_closedBall_rpow_sub_le_rpow` | same names in `SLT.Pushforward` (`Quadratic`) |
| `SLT.MiddlePositions.discDensity`, `measurable_discDensity`, `discDensity_four_thirds`, `discDensity_cubicAct_of_norm`, `lastConstT`, `lastConstT_lt_top`, `lintegral_last_le_rpow`, `lintegral_middle_le_rpow`, `enorm_rpow_mul_ofReal_mul_sq_le`, `lintegral_chart_discDensity_lt_top`, `lintegral_closedBall_discDensity_lt_top` | same names in `SLT.PositionFour` (`Upstream/Local`) |
| `SLT.MiddlePositions.Two.setLIntegral_ball_inv_rpow_le`, `setLIntegral_ball_inv_rpow_le_three_pi`, `lintegral_max_one_rpow_neg_lt_top` | same names in `SLT.Pushforward` (`Radial`) |
| `SLT.MiddlePositions.Three.volume_ball_one_complex`, `volume_closedBall_complex` | same names in `SLT.Pushforward` (`Radial`) |

Removed as exact duplicates or restatements:

| Removed | Use instead |
|---|---|
| `SLT.MiddlePositions.Two.fullPlaneQuadratic_mono`, `SLT.MiddlePositions.Three.fullPlaneQuadratic_mono` | `SLT.MiddlePositions.fullPlaneQuadratic_mono` |
| `SLT.MiddlePositions.Two.volume_ball_one` | `SLT.Pushforward.volume_ball_one_complex` |
| `SLT.MiddlePositions.toolkit_shell_two`, `toolkit_shell_three` | `SLT.MiddlePositions.shell_two`, `shell_three` |

Removed as special cases of a general lemma:

| Removed | General lemma (case) |
|---|---|
| `SLT.PositionFour.quadConst`, `quadConst_lt_top` | `SLT.Pushforward.quadConstT`, `quadConstT_lt_top` (`t = 4/3`) |
| `SLT.PositionFour.lintegral_quadratic_eq` | `SLT.Pushforward.lintegral_quadratic_eq_rpow` (`t = 4/3`) |
| `SLT.PositionFour.discConst`, `discConst_lt_top` | `SLT.Pushforward.discConstP`, `discConstP_lt_top` (`p = 1`) |
| `SLT.PositionFour.lintegral_closedBall_one_rpow_sub_le`, `lintegral_closedBall_rpow_sub_le` | `SLT.Pushforward.lintegral_closedBall_one_rpow_sub_le_rpow`, `lintegral_closedBall_rpow_sub_le_rpow` (`p = 1`) |
| `SLT.PositionFour.lastConst`, `lintegral_last_le` | `SLT.PositionFour.lastConstT`, `lintegral_last_le_rpow` (`t = 4/3`) |
| `SLT.PositionFour.lintegral_middle_le` | `SLT.PositionFour.lintegral_middle_le_rpow` |
| `SLT.PositionFour.enorm_rpow_mul_sq_le` | `SLT.PositionFour.enorm_rpow_mul_ofReal_mul_sq_le` |
| `SLT.PositionFour.lintegral_chart_lt_top` | `SLT.PositionFour.lintegral_chart_discDensity_lt_top` (`t = 4/3`) |
| `SLT.PositionFour.twoCubeDensity_cubicAct_of_norm` | `SLT.PositionFour.discDensity_cubicAct_of_norm` (`t = 4/3`) |
| `SLT.PositionFour.Downstream.shellLayer`, `measurableSet_shellLayer`, `shellLayer_volume_le` | `SLT.Pushforward.homLayer leadingMap`, `measurableSet_homLayer`, `homLayer_volume_le` |
| `SLT.PositionFour.Downstream.measurableSet_rowShell` | `SLT.Pushforward.measurableSet_homShell` (`rowShell` is now an abbreviation of `homShell (Row × Row)`) |
| `SLT.PositionFour.Downstream.volume_rowShell_lt_top`, `volume_smul_rowPair`, `norm_cube_le_one`, `norm_rowCubic_le`, `norm_leadingMap_le` | no replacement: steps of the old position-four shell proof (the explicit bound `‖R‖ ≤ 6` and the scaling of Lebesgue measure on `Row × Row`). The general lemma uses continuity on the compact shell and the Haar scaling instead |

## Overlap that remains

* Two shifted-disc bounds with different forms: `Pushforward.lintegral_ball_sub_inv_rpow_le`
  (open ball, `‖·‖ₑ⁻¹ ^ s`, constant `2π/(2-s) + π`) and
  `Pushforward.lintegral_closedBall_rpow_sub_le_rpow` (closed ball, `‖·‖ₑ ^ (-p)`, constant
  `discConstP p`). Neither is an instance of the other as stated; both proofs are kept.
* `Pushforward.lintegral_ball_rpow_neg_lt_top` (finiteness) and `Pushforward.lintegral_ball_inv_rpow`
  (exact value) cover the same integral in two forms.
* Outside the planar toolkit, some helpers are proved twice under different namespaces, for example
  `SLT.MiddlePositions.Two.measurable_F` / `SLT.MiddlePositions.Three.measurable_F`,
  `SLT.MiddlePositions.Three.F_eq` / `SLT.MiddlePositions.F_eq`, and
  `SLT.MiddlePositions.Two.one_le_W2` / `SLT.MiddlePositions.Three.one_le_W2`. They were left alone.
