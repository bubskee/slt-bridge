# slt-zoo: certified SLT examples in the shared core's vocabulary

A separate Lake package, so that the core (`../SLT`) stays mathlib-only. Each file takes a
certified Lean library for a paper and restates its headline results as
`SLT.HasLaplacePair (SLT.Z ν K) λ m`, the core's learning-pair predicate.

Tags as in the top-level `README.md`: **[LC]** Lean-certified; **[COND: H]** conditional on the named
hypothesis `H`. The tag reflects what each file imports.

| File | Source | Pin | Headline in core vocabulary |
|---|---|---|---|
| `Zoo/ResidualNetwork.lean` | [residual-slt-in-a-haystack](https://github.com/bubskee/residual-slt-in-a-haystack) (*Learning Coefficients and Active-Block Arrangements in Scalar Residual Networks*), `subDir = "lean"` | `2865e70a9ca7f559dabfce6aa32e13cf4fc88259` (paper snapshot) | [LC]: `residualNetwork_learningPair`, `global_pair_unique`, `local_pair`, worked instances `(2,2)`, `(7/6,2)`, `(7/6,1)` |
| `Zoo/VectorShear.lean` | vector-slt-lean (*Rank, Shears, and Logarithmic Multiplicity…*), local repo | `2d545cdcb9f20c34bcb188ee496d6c0261fb7289` | [LC] **unconditional**: `position_one_pair` `(4,5)`, `position_one_unique`. [COND: `ThmK`, `ThmN`]: `mainTheorem_shear_core` (table `(4,5),(4,1),(4,1),(4,1)`) and its Gaussian form |
| `Zoo/LLC.lean` | both of the above, plus core `SLT.LLC` | — | Population LLC identity (not the SGLD estimator). [LC]: `residualNetwork_llc`, `cubic_depth6_three_active_llc` (→ 2), `position_one_llc` (unconditional, → 4, `-4 log log T`). [COND: `ThmK`, `ThmN`]: `mainTheorem_shear_llc` |
| `Zoo/TemplateM.lean` | vector-slt-lean + core `SLT.Template` (brief 03, T1) | `2d545cdcb9f20c34bcb188ee496d6c0261fb7289` | [LC] **unconditional**: `ZN1_two_sided_template` (the source's `ZN1_two_sided`, same statement) and `position_one_pair_template` `(4,5)`, with the upper half through the elementary template instead of Lemma M5, `two_rows` and `theoremM` |
| `Zoo/TemplateMargin.lean` | vector-slt-lean + core `SLT.Template.Margin` (brief 03, T2) | `2d545cdcb9f20c34bcb188ee496d6c0261fb7289` | [COND: `PositionMargin`]: `thmN_of_margin`, `thmKUpper_of_margin`, `thmK_of_margin` (the source's named hypotheses `ThmN`/`ThmK` as instances of the margin template), `mainTheorem_shear_of_margin` |
| `Zoo/TemplateLeading.lean` | residual-slt + core `SLT.Template.Leading` (brief 03, T3) | `2865e70a9ca7f559dabfce6aa32e13cf4fc88259` | [LC]: `positive_homogeneous_laplace_order_template` (the source theorem on `Fin D → ℝ`, re-derived through T3 with zero remainder), `hasLaplacePair_of_homogeneous_add_remainder` (`Q + R`, with `R` of higher weight) |
| `Zoo/ReadWrite.lean` | resnet-bridge `readwrite/R0_scalar.md` (R0.1, read only, not a dependency) + core N2 | — | [LC]: one block `c = u v³`, `K = (u v³)²`: crossing `(1/6,1)`, read-dead `(1/6,1)`, write-dead `(1/2,1)` (`crossing_readDead_ne_writeDead`) |
| `Zoo/MLPArrangement.lean` | resnet-bridge `mlp/` (`s2prime_arrangement.md`, `s2pp_merged.md`, `hunt_cancellation.md`; read only, not a dependency) + core N2, M1 (brief 04, T5) | resnet-bridge `4a7060c` (S2′, S2″), `f23016c` (hunt); markdown, not a Lake dependency | [LC] **for the model losses only** (regular ⊕ monomial `J`). The network-to-model chart reduction is paper-proved, AI-reviewed and not in Lean: `outIn_ne_inOut` (`(3,1)` vs `(5/2,1)`), the other four S2′ arrangements, (both,both) `(5/2,3)` (`s2p_bothBoth`), `m4_ne_m3'` (`(9/4,1)` vs `(5/2,1)`), M2, M3, hunt `(dup,dup)` `(2,1)` |
| `Zoo/MixedGroup.lean` | resnet-bridge `readwrite/R0_scalar.md` Lemma R0.2 (read only) + core N2 | resnet-bridge `c55350b` (markdown) | [LC]: `mixedGroup_pair`, where `(w³+y)²+(w⁶+y²)²` has `J(1,1) = (7/12, 1)`, via the measure-preserving shear `y = s − w³` and a two-box squeeze. General `(p, q)` is not built |
| `Zoo/LeadingMaps.lean` | vector-slt-lean `VectorSLT/LeadingMap` + core `SLT/MiddlePositions`, `SLT/PositionFour` | `196b8df2fd0623fc7d61e8694aaede9643eaf943` | [LC]: `R2_complexify`, `R3_complexify`, `leadingMap_complexify` (the core's complex leading maps are the complexifications of the network library's real ones) and `lead_eq_zero_iff_two`, `_three`, `_four` (the `ε³` term of the network error at positions two to four vanishes exactly when the active coordinates and the core's leading map vanish) |
| `Zoo/LossComparison.lean` | vector-slt-lean `VectorSLT/LossCompare` + `Zoo/TemplateMargin.lean`, `Zoo/LeadingMaps.lean` | `196b8df2fd0623fc7d61e8694aaede9643eaf943` | [COND: `InactiveLaplace` of `Gmid 1`, `Gmid 2`, `G4`]: `mainTheorem_shear_of_inactiveLaplace` (the table `(4,5),(4,1),(4,1),(4,1)`), `thmN_of_inactiveLaplace`, `thmKUpper_of_inactiveLaplace`. The loss comparison inside `PositionMargin` is now certified in the source; what is left is `∫ e^{-N G_p} ≤ C N⁻²` on a ball of `ℝ¹²` for three explicit polynomials, with no network, target, input law, prior or cutoff in it. `ShellMargin` of the angular parts (the template's angular margin) is a sufficient condition (`mainTheorem_shear_of_shellMargin`). [LC]: `H4_zero_eq_core`, `Hmid_one_zero_eq_core`, `Hmid_two_zero_eq_core` (at `r = 0` the angular parts are the squared norms of the core's complex leading maps at real points) |

Every statement here is a corollary. The mathematics lives in the source library; the zoo only
translates it, and the core's `HasLaplacePair.unique` then shows the certified pair is the
intrinsic learning pair.

`VectorSLT` is not in the `module` system, so `Zoo/VectorShear.lean` and `Zoo.lean` are plain files.
The zoo pins `vector-slt-lean` by commit at its public repository.

Build:

```sh
cd zoo
lake exe cache get
lake build
lake env lean Audit.lean   # or ../scripts/check_audit.sh for both packages
```

Pins match `lake-manifest.json`: Lean `v4.35.0`, mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, and the two
source pins above. Audit: 205/205 zoo declarations, plus the 16 source theorems and lemmas re-checked, on
`[propext, Classical.choice, Quot.sound]`.
