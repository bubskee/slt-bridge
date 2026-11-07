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
source pins above. Audit: 25/25 zoo declarations, plus the 4 source theorems re-checked, on
`[propext, Classical.choice, Quot.sound]`.
