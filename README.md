# slt-bridge

A Lean 4 library bridging resolution of singularities and Watanabe's singular learning theory
(SLT). It has two packages:

* **the core** (`SLT/`), mathlib-only. It contains the learning-pair predicate and its algebra,
  volume ⇔ Laplace, normal crossing on boxes, the Mellin threshold, the population LLC identity and
  the two-sided Newton-polyhedron theorem;
* **the zoo** (`zoo/`), a separate package. It restates certified results from two paper libraries
  in the core's vocabulary.

The bridge itself (M3: hironaka's monomialization ⇒ existence of `(λ, m)`) is **not started** and is on hold.

## Pins

| Dependency | Pin | Where |
|---|---|---|
| Lean | `leanprover/lean4:v4.35.0` | `lean-toolchain`, `zoo/lean-toolchain` |
| mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` | `lakefile.toml`, `zoo/lakefile.toml` |
| hironaka (planned for M3, **not yet a dependency**) | tag `v4.35.0` = `044d89c9455859446fc5e986667319f910e15f4b` | commented out in `lakefile.toml` |
| residual-slt-in-a-haystack (zoo only) | `2865e70a9ca7f559dabfce6aa32e13cf4fc88259`, `subDir = "lean"` | `zoo/lakefile.toml`, `zoo/lake-manifest.json` |
| vector-slt-lean (zoo only, local git path, no remote) | `2d545cdcb9f20c34bcb188ee496d6c0261fb7289` | `zoo/lakefile.toml`, `zoo/lake-manifest.json` |

## Layout

```
SLT/Laplace/       Rate, Pair (HasLaplacePair), Integral (Z, V, comparability, bridges),
                   Volume (volume ⇔ Laplace, layer cake), Mellin (Mellin identity and threshold)
SLT/NormalCrossing Step (one-coordinate integration), Cube ((0,1]^d), Box ([-δ,δ]^d, with units)
SLT/LLC/           Identity (L1, L2), Pointwise (antitonicity, regular-variation limit)
SLT/Newton/        Lower (N1), Statement (N2 as a Prop), Sanity, TwoSided (N2 proof), Box (N2 with units);
                   Polytope, Tube, LogCoords, Upper, LowerTwo are the N2 proof's intermediate steps
Audit.lean         #print axioms for every public core declaration
zoo/Zoo/           ResidualNetwork, VectorShear, LLC          zoo/Audit.lean  the same for the zoo
scripts/           check_audit.sh (audit completeness + axioms), DumpDecls.lean, Lint.lean, LintZoo.lean
docs/status_log.md per-milestone log          PLAN.md  Phase 0 plan, roadmap, questions (§7)
```

## Build and audit

```sh
lake exe cache get && lake build              # core
(cd zoo && lake exe cache get && lake build)  # zoo
scripts/check_audit.sh                        # both audits, completeness, and a sorry scan
lake env lean scripts/Lint.lean               # Batteries environment linters over SLT
(cd zoo && lake env lean ../scripts/LintZoo.lean)  # and over Zoo
```

Both packages build with Mathlib's standard linter set (`weak.linter.mathlibStandardSet`) and
**zero warnings in our sources**. The header linter is off because it enforces Mathlib's own
"Authors:" layout. The zoo build prints warnings from the pinned `vector-slt-lean`; that repository
is read-only for us. `check_audit.sh` checks three things: every public declaration of `SLT` and `Zoo`
has a `#print axioms` line (exclusions go in `scripts/audit_exclude.txt`, currently empty); every
reported axiom is among `propext`, `Classical.choice`, `Quot.sound`; and there is no
`sorry`/`admit`/`native_decide`.

**Current counts:** core 243/243 public declarations audited; zoo 25/25, plus 4 source theorems
re-checked. All are on `[propext, Classical.choice, Quot.sound]`. `#print axioms` is transitive, so
the `private` helpers are covered by the public theorems that use them.

## Conventions

* **`Z` is `ℝ≥0∞`-valued:** `Z ν K N = ∫⁻ x, ofReal (exp (-(N * K x))) ∂ν` (a `lintegral`), so it
  carries no integrability side conditions. The real/Bochner form `Zr` and the scalar library's
  `HasLaplaceOrder` are reached through bridges (`Zr_eq_integral`, `hasLaplacePair_Z_iff_hasLaplaceOrder`).
* **`HasLaplacePair F λ m`** means `c N^{-λ} (log N)^{m-1} ≤ F N ≤ C N^{-λ} (log N)^{m-1}` eventually
  along `atTop`, **with `1 ≤ m`**. That makes `(λ, m)` unique (`HasLaplacePair.unique`). Explicit-`N₀`
  forms are `laplaceLower_iff` and `laplaceUpper_iff`.
* **Boxes:** normal crossing uses `box δ = [-δ,δ]^d` and the cube `(0,1]^d`. The Newton theorem
  (N1/N2) is stated on `[0,1]^d` (`Icc 0 1`) with Lebesgue measure, and `newton_box_units` moves it
  to `[-δ,δ]^d` with a prior density between two positive constants. Coordinates are `Fin d → ℝ`.
* **Newton distance:** `newtonDist Γ = t* = max_{u ∈ Δ} min_{α ∈ Γ} ⟨α, u⟩` (the sSup of certified `t`).
* **Newton multiplicity: `m = dim O + 1` by definition** (`newtonMult`). Here
  `O = optWeights Γ` is the set of optimal simplex weights, and `dim` is the dimension of its affine
  span. By LP duality this equals the classical `d − dim F`, where `F` is the smallest face of the
  Newton polyhedron through `t*·𝟙`. **That equivalence is not formalised.** The sanity lemmas in
  `SLT/Newton/Sanity.lean` pin the convention on the standard examples
  (`{2k}` → 1, `x²y²` → 2, `x² + y²` → 1, `x²` in `d = 2` → 1).
* **LLC:** every LLC statement here is the **population** identity for the tempered posterior
  `E_t[K]` (deterministic, exact integrals). None of them is about the SGLD estimator.

## Coverage

Tags: **[LC]** Lean-certified: proved, audited, and its hypotheses are ordinary mathematical ones.
**[COND: H]** Lean-certified *conditional on the named hypothesis `H`*, which is an unproved
statement passed as an argument. **[STMT]** statement only.

### Core (`SLT`)

| Item | Lean | Tag |
|---|---|---|
| M1 learning pair, uniqueness | `HasLaplacePair`, `HasLaplacePair.unique` | [LC] |
| M1 comparability, priors, densities | `HasLaplacePair.of_comparable`, `.of_prior`, `.withDensity` | [LC] |
| M1 sums and products | `hasLaplacePair_finset_sum`, `exists_hasLaplacePair_finset_sum` (min λ, max m), `HasLaplacePair.mul`, `.finset_prod`, `.prod` | [LC] |
| M1 volume ⇔ Laplace | `Z_eq_layercake`, `laplaceLower_of_volume`, `laplaceUpper_of_volume`, `laplaceUpper_iff_volume` | [LC] |
| M1 bridges to the scalar and vector libraries and to grammar's form | `hasLaplacePair_ofReal_iff`, `hasLaplacePair_Z_iff_hasLaplaceOrder`, `hasLaplacePair_Z_of_hasLaplaceOrder`, `hasLaplacePair_iff_bounds`, `hasLaplacePair_Z_iff_isTheta` | [LC]. The scalar and vector adapters are kernel-checked against their sources in the zoo; the grammar (`IsTheta`) form is matched by reading only, since grammar is not a dependency |
| M2 normal crossing | `NC.ncZ_hasLaplacePair` (cube), `normalCrossing_box`, `normalCrossing_box_units` | [LC] |
| M2 Mellin threshold | `mellin_Z`, `lintegral_rpow_neg_lt_top_iff` (`∫K^{-s} < ∞ ⇔ s < λ`) | [LC] |
| L1 LLC identity (population) | `hasDerivAt_log_Zr` (`(log Z)' = -E_t[K]`), `integral_gibbsMean`, `antitoneOn_gibbsMean` | [LC] |
| L2 log-averaged LLC (population) | `llc_log_average`, `tendsto_llc_log_average` | [LC] |
| L4 pointwise `t E_t[K] → λ` (population) | `tendsto_mul_gibbsMean_of_regularVariation` | [LC]: regular variation of `Z` is an explicit hypothesis, not proved for analytic `K` |
| N1 Newton lower bound, `λ ≤ 1/t*` | `newton_laplaceLower`, `newton_lambda_le`, `newtonDist_*` sanity values | [LC] |
| N2 two-sided Newton theorem | `NewtonTwoSided d : Prop`, proved as `newtonTwoSided`; `hasLaplacePair_monoSum` | [LC] |
| N2 with units on `[-δ,δ]^d` | `newton_box_units` | [LC] |
| N2 multiplicity sanity | `optWeights_*`, `newtonMult_*` | [LC] |
| `m = dim O + 1 ⇔ m = d − dim F` (LP duality) | not in Lean | not formalised |
| M3 monomialization ⇒ `(λ, m)` exists | not started | on hold |

### Zoo (`Zoo`), tagged by what each row imports

| Item | Lean | Imports | Tag |
|---|---|---|---|
| Scalar ResNet adapter | `hasLaplaceOrder_iff` (`Iff.rfl`) | residual-slt `2865e70` | [LC] |
| Scalar ResNet global pair, intrinsic | `residualNetwork_learningPair`, `global_pair`, `global_pair_unique` | residual-slt `2865e70` | [LC] (the paper's hypotheses; the certificate is built by `unified_residual_network_certificate`) |
| Scalar ResNet local pairs, worked instances | `local_pair`, `cubic_depth6_three_active` `(2,2)`, `cubic_depth5_local_split13` `(7/6,2)`, `_split22` `(7/6,1)` | residual-slt `2865e70` | [LC], given the paper's certificate as a hypothesis |
| Vector adapter | `ofVector`, `toVector` | vector-slt-lean `2d545cd` | [LC] |
| Vector shear, position 1 | `position_one_pair` `(4,5)`, `position_one_unique` | vector-slt-lean `2d545cd` | [LC], **unconditional** |
| Vector shear, position table | `mainTheorem_shear_core`, `mainTheorem_shear_gaussian_core` `(4,5),(4,1),(4,1),(4,1)` | vector-slt-lean `2d545cd` | [COND: `ThmK`, `ThmN`] |
| Positions differ | `position_one_ne_position` | vector-slt-lean `2d545cd` | [LC] (takes the two pairs as hypotheses) |
| LLC, scalar ResNet (population) | `residualNetwork_llc_log_average`, `residualNetwork_llc`, `cubic_depth6_three_active_llc` | residual-slt + core L2 | [LC] |
| LLC, vector position 1 (population) | `position_one_llc` (→ 4, with `-4 log log T`) | vector-slt-lean + core L2 | [LC], **unconditional** |
| LLC, vector position table (population) | `mainTheorem_shear_llc` | vector-slt-lean + core L2 | [COND: `ThmK`, `ThmN`] |

The four source theorems the zoo uses (`ResidualSLT.unified_residual_network_certificate`,
`VectorSLT.ZN1_two_sided_moments`, `VectorSLT.mainTheorem_shear`,
`VectorSLT.mainTheorem_shear_gaussian`) are re-audited in `zoo/Audit.lean`. `ThmK` and `ThmN` are
hypotheses, not axioms, so they do not appear in any audit line.

## Licence

Apache-2.0; see `LICENSE`.
