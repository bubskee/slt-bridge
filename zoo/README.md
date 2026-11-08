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
| `Zoo/MLPArrangement.lean` | resnet-bridge `mlp/` (`s2prime_arrangement.md`, `s2pp_merged.md`, `hunt_cancellation.md`; read only, not a dependency) + core N2, M1 (brief 04, T5) | resnet-bridge `4a7060c` (S2′, S2″), `f23016c` (hunt); markdown, not a Lake dependency | [LC] **for the model losses only** (regular ⊕ monomial `J`). The network-to-model chart reduction is paper-proved, AI-reviewed and not in Lean: `outIn_ne_inOut` (`(3,1)` vs `(5/2,1)`), the other four S2′ arrangements, `m4_ne_m3'` (`(9/4,1)` vs `(5/2,1)`), M2, M3, hunt `(dup,dup)` `(2,1)` |

Every statement here is a corollary. The mathematics lives in the source library; the zoo only
translates it, and the core's `HasLaplacePair.unique` then shows the certified pair is the
intrinsic learning pair.

`VectorSLT` is not in the `module` system, so `Zoo/VectorShear.lean` and `Zoo.lean` are plain files.
`vector-slt-lean` has no remote yet; the zoo pins it by local git path.

Build:

```sh
cd zoo
lake exe cache get
lake build
lake env lean Audit.lean   # or ../scripts/check_audit.sh for both packages
```

Pins match `lake-manifest.json`: Lean `v4.35.0`, mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, and the two
source pins above. Audit: 76/76 zoo declarations, plus the 11 source theorems and lemmas re-checked, on
`[propext, Classical.choice, Quot.sound]`.
