# slt-zoo: certified SLT examples in the shared core's vocabulary

A separate Lake package, so that the core (`../SLT`) stays mathlib-only. Each file takes a
certified Lean library for a paper and restates its headline results as
`SLT.HasLaplacePair (SLT.Z ν K) λ m`, the core's learning-pair predicate.

| File | Source | Pin | Headline in core vocabulary |
|---|---|---|---|
| `Zoo/ResidualNetwork.lean` | [residual-slt-in-a-haystack](https://github.com/bubskee/residual-slt-in-a-haystack) (*Learning Coefficients and Active-Block Arrangements in Scalar Residual Networks*) | `2865e70` (paper snapshot) | `residualNetwork_learningPair`, `global_pair_unique`, `local_pair`, worked instances `(2,2)`, `(7/6,2)`, `(7/6,1)` |
| `Zoo/VectorShear.lean` | vector-slt-lean (*Rank, Shears, and Logarithmic Multiplicity…*), local repo | `2d545cd` | `position_one_pair` (unconditional `(4,5)`), `position_one_unique`, `mainTheorem_shear_core` (table `(4,5),(4,1),(4,1),(4,1)`, conditional on `ThmK`/`ThmN`), Gaussian form |

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
lake env lean Audit.lean
```
