# slt-bridge status log

Moved here from `PLAN.md` §9 in brief 02 (cleanliness pass). Entries are kept as written at the time,
except that each heading now gives its commit. Audit counts in an entry are the counts *at that
stage*; the current counts are in `README.md` and are checked by `scripts/check_audit.sh`.
Brief 02 made 54 core and 5 zoo helpers `private` (no statement changes), so some helper names
mentioned below are no longer public.

### M1: G1 core v0 (2026-11-07). Committed `ae987f2`

`lake build`: 0 errors, 0 warnings. `lake env lean Audit.lean`: **91/91 declarations depend on axioms
`[propext, Classical.choice, Quot.sound]`**. 0 `sorry`/`admit`/`native_decide`. **[LC]** About 1.1k lines, `module` style,
`public import Mathlib`.

| File | Contents |
|---|---|
| `SLT/Laplace/Rate.lean` | `rate λ m N = N^{-λ}(log N)^{m-1}`, `Dominates`, `rate_isLittleO` (strict domination ⇒ `o`), `rate_le_of_dominates`, `exp_neg_isLittleO_rate`, `rate_add`, `rate_comp_mul_bounds` |
| `SLT/Laplace/Pair.lean` | `LaplaceLower`/`LaplaceUpper` (eventually, `atTop`), `HasLaplacePair` (with `1 ≤ m`); `hasLaplacePair_iff_bounds` (vector body); mono/congr/const_mul/comp_mul; `of_dominates`, `laplaceUpper_of_exp`; sums `hasLaplacePair_finset_sum`, `exists_hasLaplacePair_finset_sum` (λ = min, m = max among minimisers); products `HasLaplacePair.mul`, `.finset_prod`; **`HasLaplacePair.unique`**; `HasLaplaceOrder` (scalar body) with `hasLaplacePair_ofReal_iff`; `hasLaplacePair_ofReal_iff_isTheta` |
| `SLT/Laplace/Integral.lean` | `Z`, `V`; loss comparability (a.e.) `HasLaplacePair.of_comparable`; priors `of_prior`, `withDensity`; `Z_prod`, `HasLaplacePair.prod`; `Z_ge_V`, `V_le_Z`; gluing pieces `Z_restrict_iUnion_le`, `laplaceUpper_of_loss_ge`; Bochner bridge `hasLaplacePair_Z_iff_hasLaplaceOrder`, `hasLaplacePair_Z_iff_isTheta` (grammar form) |
| `SLT/Laplace/Volume.lean` | layer cake `Z_eq_layercake`, `gammaLog`; `laplaceLower_of_volume`, `laplaceUpper_of_volume`, `volume_global_of_local`, `volume_le_of_laplaceUpper`, **`laplaceUpper_iff_volume`** (finite ν) |
| `Audit.lean` | `#print axioms` for every declaration |

Design decisions (open to review):
- The canonical object is `ℝ≥0∞`-valued (`lintegral`), so there are no integrability side conditions. Real and Bochner forms are reached through bridges.
- `HasLaplacePair` requires `1 ≤ m`. That makes `(λ, m)` unique; with `m = 0` allowed, `m = 0` and `m = 1` would give the same rate.
- Eventual bounds use `∀ᶠ N in atTop` rather than `∃ N₀`. The vector library's explicit forms are `laplaceLower_iff`/`laplaceUpper_iff`.
- The adapters are stated as body-level equivalences. They are **not yet** checked against the other libraries with a Lake
  dependency (we don't depend on them). `SLT.HasLaplaceOrder` has the body of `ResidualSLT.HasLaplaceOrder` copied verbatim,
  and the right side of `hasLaplacePair_iff_bounds` is `1 ≤ m ∧` the vector body.

Deferred from M1: `Z` over `Measure.pi` (Mathlib only has the Bochner `integral_fintype_prod_eq_prod`; the abstract
`finset_prod` is done); the scalar library's critical/power-only predicates; the Mellin threshold (planned for M2).

### M2: normal crossing v1 + Mellin threshold (2026-11-07). Committed `2162565`

`lake build` is clean (0 errors, 0 warnings). `lake env lean Audit.lean`: **169/169 declarations (M1 + M2) depend on
`[propext, Classical.choice, Quot.sound]`**. 0 `sorry`. **[LC]** M2 added about 1.4k lines.

| File | Contents |
|---|---|
| `SLT/NormalCrossing/Step.lean` | `NC.stepG`, `NC.NCBound` and the one-coordinate step lemmas, ported from `vector-slt-lean` with exponent `2k` generalised to any `k ≥ 1`; the split point there is retuned from `N^{-1/(4k)}` to `N^{-1/(2k)}` |
| `SLT/NormalCrossing/Cube.lean` | `NC.ncZ k h` on `(0,1]^d` with `x^{kᵢ}`, **inactive coordinates `kᵢ = 0` allowed**; `ncLam` = min over active `(hᵢ+1)/kᵢ`, `ncMult` = #argmin; `NC.ncZ_cases` (all inactive ⇒ `c e^{-N}`, else `NCBound`), **`NC.ncZ_hasLaplacePair`** |
| `SLT/NormalCrossing/Box.lean` | box `[-δ,δ]^d`, `absLoss k = ∏|yᵢ|^{kᵢ}`, `absDens h = ∏|yᵢ|^{hᵢ}`; reflections (`measurePreserving_refl`), `Z_box_le` (≤ 2^d · orthant), scaling `Z_pos_scale` (linear-map change of variables); **`normalCrossing_box`**, **`normalCrossing_box_units`**: loss between `c·K` and `C·K`, prior density between `a·∏|y|^h` and `b·∏|y|^h` on the box ⇒ the pair `(ncLam, ncMult)`. This is the chart-local statement G2 will feed. |
| `SLT/Laplace/Mellin.lean` | `lintegral_rpow_mul_exp_neg` (Gamma), **`mellin_Z`**: `∫₀^∞ t^{s-1}Z(t)dt = Γ(s)∫K^{-s}dν`; **`lintegral_rpow_neg_lt_top_iff`**: given the pair, `∫K^{-s}dν < ∞ ⇔ s < λ` for `s > 0` (finite ν, K > 0 a.e.) |

Still open for G2: centring the box at a chart point `c` (a translation, which is measure-preserving); `EuclideanSpace` ↔ `Fin n → ℝ`;
and integer exponents `hᵢ` coming from the Jacobian, which are covered as the real `hᵢ > -1` case. The Mellin threshold isn't yet
specialised to the box (that needs `K > 0` a.e. on the box, i.e. coordinate hyperplanes are null).

### G6 zoo, part 1: scalar ResNet (2026-11-07). Committed `3469e76`

There's a new package `zoo/` (it requires the core via `path = ".."`, plus `residual-slt-in-a-haystack` @ `2865e70`, the paper's
snapshot, `subDir = "lean"`). The core itself stays mathlib-only. One new core lemma: `hasLaplacePair_Z_of_hasLaplaceOrder`, which
goes from the scalar predicate on the Bochner integral to `HasLaplacePair (Z ν K)` with *no* side conditions (the lower bound
forces integrability). Core audit: 170/170 clean. Zoo audit (`zoo/Audit.lean`): 9/9 clean, plus
`ResidualSLT.unified_residual_network_certificate` re-checked here with the standard three axioms. **[LC]**

`zoo/Zoo/ResidualNetwork.lean`:
- `hasLaplaceOrder_iff : ResidualSLT.HasLaplaceOrder ℓ m Z ↔ SLT.HasLaplaceOrder ℓ m Z := Iff.rfl`, so the M1 adapter is now kernel-checked.
- `residualNetwork_learningPair` (the paper's hypotheses ⇒ core `HasLaplacePair` with `globalLearningPair r k (L-k)`), `global_pair`,
  **`global_pair_unique`** (the certified pair is the intrinsic one), `local_pair` (Theorem 2 on small balls).
- Instances: `cubic_depth6_three_active` (pair `(2,2)`), `cubic_depth5_local_split13` `(7/6, 2)`, `cubic_depth5_local_split22` `(7/6, 1)`.

**Vector shear: blocked by a namespace clash.** `vector-slt-lean` declares 24 constants that also exist in the core under the same names
(`SLT.Z`, `SLT.V`, `SLT.HasLaplacePair`, `SLT.LaplaceLower`, `SLT.Z_prod`, `SLT.gammaLog`, …), so one file can't import both.
The translation itself is trivial: `mainTheorem_shear` concludes vector `SLT.HasLaplacePair (Zpos …) λ m`, which is exactly the
right side of the core's `hasLaplacePair_iff_bounds` (with `1 ≤ m`). Bobby's decision is needed on how to resolve the clash.

### G6 zoo, part 2: vector shear (2026-11-07). Committed `4f9ce42`

vec-lean renamed its namespace (`SLT` → `VectorSLT.SLT`, commit `2d545cd`, no mathematical change), and the zoo pins it by local
git path. `zoo/Zoo/VectorShear.lean` is a plain file, because `VectorSLT` isn't `module`-style. It contains:
- `ofVector`/`toVector`: vector pair + `1 ≤ m` ⇔ core pair, kernel-checked through `hasLaplacePair_iff_bounds`.
- **`position_one_pair`**: unconditional core pair `(4,5)` for `Z_{N,1}` (from `ZN1_two_sided_moments`); `position_one_unique`.
- `mainTheorem_shear_core`, `mainTheorem_shear_gaussian_core`: the table `(4,5),(4,1),(4,1),(4,1)`, **conditional on the
  hypotheses `ThmK`, `ThmN`**, as in the source. `position_one_ne_position`.

Zoo audit: 16/16 zoo declarations, plus the four source theorems re-checked here, on `[propext, Classical.choice, Quot.sound]`.
`ThmK`/`ThmN` are hypotheses, not axioms, so they don't appear in the audit. Keep the [LC] / conditional labels distinct
when citing this in the paper.

(Commits since: M1 `ae987f2`, M2 `2162565`, zoo part 1 `3469e76`, zoo part 2 `4f9ce42`.)

### Brief 01, stage L: LLC identity (2026-11-07). Committed `ebff403`

Core `SLT/LLC/Identity.lean`, `SLT/LLC/Pointwise.lean`; zoo `zoo/Zoo/LLC.lean`. Setting: `ν` finite, `K` measurable, `K ≥ 0` a.e.
**No boundedness of `K` is used** (domination comes from `u e^{-su} ≤ 1/s`); `Z > 0` needs only `ν ≠ 0`, and L2 derives that from the
lower Laplace bound. All statements are population and deterministic, not about the SGLD estimator (the docstrings say so).
- L1 `hasDerivAt_log_Zr`: `(log Z)'(t) = -E_t[K]` for `t > 0`. Integrated form: `integral_gibbsMean`.
- L1 optional `antitoneOn_gibbsMean`, via mathlib's `cgf` (`log Z = cgf (-K) ν`, `iteratedDeriv_two_cgf_eq_integral`).
- L2 `llc_log_average`: `|∫_{t₀}^T E_t dt - (λ log T - (m-1) log log T)| ≤ C` eventually. `tendsto_llc_log_average`: `/log T → λ`.
- L3: `residualNetwork_llc(_log_average)`, `cubic_depth6_three_active_llc` (→ 2), **`position_one_llc`** (unconditional: → 4,
  with `-4 log log T`), `mainTheorem_shear_llc` (conditional on `ThmK`/`ThmN`: all positions → 4, `log log` term distinguishes
  position one). Added on the way: `measurable_popLossA` (via joint continuity of `net`) and `Zpos_eq_Z` (`Zpos` is core `Z` for
  `posPrior = volume.withDensity (φ · χ(· - θ_p))`, given measurable `φ`, `χ`).
- L4 `tendsto_mul_gibbsMean_of_regularVariation`: `Z(at)/Z(t) → a^{-λ}` ∀a>0 ⇒ `t E_t[K] → λ`. Regular variation for analytic `K`
  is **not** attempted (it needs leading-coefficient asymptotics, §4.3).
Audits: core 185/185, zoo 28/28, all `[propext, Classical.choice, Quot.sound]`. **[LC]** No `sorry`.

(Stage L committed `ebff403`.)

### Brief 01, stage N: N1 + N2 statement (2026-11-07). Committed `18d59e3` (with N2)

`SLT/Newton/Lower.lean`: `monomial`, `IsNewtonCert`, `newtonDist` (max–min form, `sSup` of certified `t`; the LP-duality equivalence
with `min{t | t𝟙 ∈ Γ₊}` is not formalised). `newton_laplaceLower` (`K ≤ CΣ|w|^α` on `[0,1]^d`, plus a certificate `(t,u)` ⇒
`LaplaceLower Z (1/t) 1`, via one anisotropic box) and `newton_lambda_le` (`λ ≤ 1/t*`). The `t*` sanity values for the brief's
table are all proved. `SLT/Newton/Statement.lean`: `optWeights`, `newtonMult = dim affineSpan(optimal weights) + 1` (= `d − dim F` by
duality, not formalised), and `NewtonTwoSided d : Prop`, the N2 statement with no proof and no `sorry`. Core audit 200/200 clean. **[LC]** for N1.
N3 cost note is in the shared notes (`slt-bridge_brief01_N.md`). Rank-1 RRR at true rank 0 is exactly a monomial sum and is the best
first target. Vector shear position 1 is *not* N2-comparable (`m = 5` ≠ N2's `m = 1`).

### Brief 01, stage N2: two-sided Newton theorem, proved (2026-11-07). Committed `18d59e3`

`newtonTwoSided : NewtonTwoSided d` is the statement exactly as Bobby approved it, unchanged. It has no LP duality and no `sorry`. **[LC]**

| File | Content |
|---|---|
| `Newton/Sanity.lean` | Bobby's addition 1: `O` computed explicitly, giving `newtonMult` = 1, 2, 1, 1 on the brief's table |
| `Newton/Polytope.lean` | Extreme points of finite systems are basic. Finitely many vertices give a gap; finitely many slide directions give a bound. **Hoffman-type** `dualSlab_subset`: `P_η ⊆ P_0 + B(Cη)` for small `η`, via Krein–Milman |
| `Newton/Tube.lean` | `volume_thicken_le`: a compact set of affine dimension `k`, thickened by `r`, has volume `≤ C r^{d−k}` (minimal injective coordinate set, antilipschitz map, Fubini) |
| `Newton/LogCoords.lean` | `w = e^{−x}` change of variables (Jacobian `e^{−⟨𝟙,x⟩}`); `V(s)` lies between `H(log(|Γ|/s))` and `H(log(1/s))`; `t*` is attained |
| `Newton/Upper.lean` | `Hfun_le`: `H(L) ≤ C e^{−L/t*} L^{dim O}` (shells, plus slab and tube) |
| `Newton/LowerTwo.lean` | `Hfun_ge`: `H(L) ≥ c e^{−L/t*} L^{dim O}`, as an explicit injective linear image of a sheared box built from `dim O + 1` independent optimal weights |
| `Newton/TwoSided.lean` | `hasLaplacePair_monoSum`, `newtonTwoSided` |
| `Newton/Box.lean` | Bobby's addition 2: `newton_box_units`, on `[−δ,δ]^d` with a prior density between constants, via reflections and scaling |

Core audit: 226/226 clean. The zoo rebuilds. About 2050 lines in `SLT/Newton/`.

### Brief 03, T1: the elementary template (2026-11-07, overnight run 04). Branch `overnight-templates`

**[LC]** on `[propext, Classical.choice, Quot.sound]`: core 262/262, zoo 49/49 plus 9 source
theorems and lemmas. Zero warnings in our sources, Batteries lint clean, no `sorry`.

- `SLT/Template/Elementary.lean`: `WeakL1`, `lintegral_min_le_of_weakL1` (weak-L¹ costs one log,
  by the layer cake), `MinLogBound` (`∫ min(T, s w) ≤ s(B + D log⁺(1/s))`), `WeakL1.minLogBound`,
  `MinLogBound.comp_preimage`.
- `SLT/Template/Cone.lean`: `minLogBound_pivotCone`. A weight `|r|^{-(n+1)} h_r(q)` on the pivot
  cone, with `∫ h_r ≤ H` uniformly in `r`, satisfies `MinLogBound`. This is Theorem M's M5 in general
  form. The first draft asked for weak-L¹ instead; that is false when `h_r` depends on `r` (the
  weights move with the amplitudes), so the min-integral form is the right hypothesis.
- `SLT/Template/Fibre.lean`: `lintegral_le_rate_of_minLogBound` (explicit constant `fibreConst`,
  uniform over any family sharing `(A, B, D, λ)`), `laplaceUpper_of_minLogBound`,
  `laplaceUpper_of_integrable`, `hasLaplacePair_of_minLogBound` (the template), and
  `lintegral_triangular` (two blocks coupled one way, Theorem M's F5).
- Guardrail, `zoo/Zoo/TemplateM.lean`: `ZN1_two_sided_template` has the source statement of
  `VectorSLT.ZN1_two_sided`. The upper half goes through the template: `pivotRow_template` (Lemma M4
  + Lemma M3 through `minLogBound_pivotCone` + `lintegral_le_rate_of_minLogBound`),
  `J_bound_template` (`lintegral_triangular`), and `LaplaceUpper` calculus for the assembly. The
  source's `lemmaM5`, `pivotRow`, `two_rows`, `J_bound`, `UM_bound` and `theoremM` are not used.
  The source's coordinate plumbing (`rowBound`'s pivot covering, `UM_bound`'s Fubini, `theoremM`'s
  pointwise comparison) is reproduced in the zoo file with the template's constants.
