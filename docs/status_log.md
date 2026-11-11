# slt-bridge status log

Moved here from the project plan (kept outside this repository) in brief 02 (cleanliness pass). Entries are kept as written at the time,
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

### Brief 03, T2: the margin template (2026-11-07, overnight run 04). Branch `overnight-templates`

**Tags.** The template is **[LC]** conditional on the named hypothesis `AngularMargin`. The zoo instance is
[COND: `PositionMargin`].

**Checks.** Core 277/277 and zoo 56/56 audited, plus 10 source theorems, all on
`[propext, Classical.choice, Quot.sound]`. Zero warnings, lint clean, no `sorry`.

- **`SLT/Template/Margin.lean`.**
  - `AngularMargin` (named hypothesis): weighted homogeneity `G(rξ) = r^{2d} H(r,ξ)` on the shell, and
    `∫_shell H^{-s} ≤ M` uniformly in `r`.
  - Proved:
    - `lintegral_eq_shell_average`: radial coordinates without spheres, by averaging over dyadic shells;
    - `exp_neg_le_rpow`;
    - `lintegral_radial_min_le`;
    - `lintegral_exp_le_of_angularMargin`: the radial split (K24), `N^{-D/(2d)}` with no log when `2ds > D`;
    - `lintegral_exp_neg_sum_sq`: the active Gaussian factor;
    - `laplaceUpper_of_angularMargin` and `hasLaplacePair_of_angularMargin`: rate `(a/2 + D/(2d), 1)`.
  - `angularMargin_norm_pow` shows the hypothesis is satisfiable.
- **Guardrail, `zoo/Zoo/TemplateMargin.lean`.**
  - `PositionMargin` packages Theorem K §§1, 6 and Proposition N2's inputs at one position: the (K3) active
    coordinates and comparison, plus `AngularMargin` with `D = 12`, `d = 3`, `s > 2`.
  - `thmN_of_margin`, `thmKUpper_of_margin`, `thmK_of_margin`: `ThmN`/`ThmK` are instances, since
    `4/2 + 12/6 = 4`.
  - `mainTheorem_shear_of_margin`: the position table with margins in place of `ThmK`/`ThmN`.
- **Hironaka.** The project plan (kept outside this repository) records the discharge route and a design risk: the paper transfers from complex to
  real variables once, at the ambient level, while the hypothesis here is real and uniform in `r`.

### Brief 03, T3: leading map plus higher-weight remainder (2026-11-07, overnight run 04). Branch `overnight-templates`

**[LC]**: core 286/286, zoo 60/60 plus 11 source theorems, all on `[propext, Classical.choice, Quot.sound]`.
Zero warnings, lint clean.
- **`SLT/Template/Leading.lean`.**
  - `IsHomogeneous`, `HigherWeightRemainder`.
  - `shell_bounds_of_homogeneous`: compactness on the shell.
  - `angularMargin_of_leading`: T2's named hypothesis, discharged for nondegenerate leading parts.
  - `laplaceUpper_of_leading`, and `laplaceLower_of_leading` (a ball of radius `N^{-1/(2d)}`).
  - `hasLaplacePair_of_leading`, `exists_hasLaplacePair_of_leading`.
- **Guardrail, `zoo/Zoo/TemplateLeading.lean`.** `positive_homogeneous_laplace_order_template` re-derives
  `ResidualSLT.positive_homogeneous_laplace_order` on `Fin D → ℝ` with Lebesgue measure: both halves, zero
  remainder, the source statement. `hasLaplacePair_of_homogeneous_add_remainder` is the form a new
  architecture checks.
- **Obstruction note, `docs/T3_obstruction.md`.**
  - The degenerate case needs stability.
  - rw-bridge's `u v³` blocks are degenerate and go through N2.
  - Anisotropic weights are not built.
  - The (K3) construction for `PositionMargin` is costed at 600–1000 lines per position.
- **Tooling.** `scripts/check_audit.sh` now joins the pretty-printer's wrapped axiom lists. Long theorem names
  had made it misreport clean entries as unexpected.

### Brief 03, T4: one factored read/write block (2026-11-07, overnight run 04). Branch `overnight-templates`

**[LC]**: zoo 76/76 plus 11 source theorems; core unchanged at 286/286. All on
`[propext, Classical.choice, Quot.sound]`. Zero warnings, lint clean.

`zoo/Zoo/ReadWrite.lean` covers one block `c = u v³` with target `c* = 0` and local loss `K = (u v³)²`, from
resnet-bridge R0.1 (read only). It uses the core's `newton_box_units` and Lebesgue prior on a box around
the point; `Z_translate` moves the box to the origin.

| Stratum | `Γ` | Lean | Pair |
|---|---|---|---|
| Crossing `(0,0)` | `{(2,6)}` | `oneBlock_crossing_pair` | `(1/6, 1)` |
| Read-dead `(u*,0)` | `{(0,6)}` | `oneBlock_readDead_pair`, `δ ≤ \|u*\|/2` | `(1/6, 1)` |
| Write-dead `(0,v*)` | `{(2,0)}` | `oneBlock_writeDead_pair`, `δ ≤ \|v*\|/2` | `(1/2, 1)` |

`crossing_readDead_ne_writeDead` states R0.1's dichotomy.

**Two-block identity group `K = (u₁v₁³ + u₂v₂³)²` at the origin: [unverified], not built.**
- **Not comparable to a monomial sum.** `K` vanishes on the cancellation hypersurface `u₁v₁³ = -u₂v₂³`, not
  only on coordinate planes. So N2 does not apply.
- **The Newton polygon gives `t* = 3`.** `Γ(K) = {(2,6,0,0), (0,0,2,6), (1,3,1,3)}`. The cross term is the
  average of the other two, so `t* = max_u min(2u₁+6u₂, 2u₃+6u₄) = 3` at `u = (0,½,0,½)`, giving `1/t* = 1/3`.
- **But the face is degenerate.** Its principal part `u₁v₁³ + u₂v₂³` has real zeros in the torus, so
  Varchenko's equality is not guaranteed.
- **An independent heuristic gives the same value.** Each `cᵢ` has density `≍ |cᵢ|^{-2/3}` (R0.1). The sum
  `s = c₁ + c₂` then has density `≍ |s|^{-1/3}`, and `∫ e^{-Ns²} |s|^{-1/3} ds ≍ N^{-1/3}`.
- **Expected pair: `(1/3, 1)`. This is AI-computed and not Lean-certified.** The forum's guess of `1/6` does not
  match either computation.
- **Route to a certificate.** The cancellation is exactly the T2/T3 degenerate case. A certificate could go
  through the pushforward sandwich (R0.0) plus a 1-D convolution bound; neither is built.

## Brief 03: closing summary (proof templates, overnight run 04)

**Branch `overnight-templates`**, cut from `1d21178`. It is not merged and not pushed; Bobby merges. The commits
are T1 `df4501d`, T2 `85285a4` plus `ddcbca8` (notes), T3 `d0b6096`, and T4 (this entry). The forum verified
each stage independently.

| Stage | Template (core) | Guardrail (zoo) | Tag |
|---|---|---|---|
| T1 elementary | `SLT/Template/{Elementary,Cone,Fibre}`: `MinLogBound`, the pivot-cone M5, slice ⇒ rate, triangular Fubini, `hasLaplacePair_of_minLogBound` | `ZN1_two_sided_template`: vector-slt-lean's `ZN1_two_sided` re-derived without `lemmaM5`/`two_rows`/`theoremM`; same statement | [LC] |
| T2 margin | `SLT/Template/Margin`: named hypothesis `AngularMargin`; the radial split (K24) is proved | `thmN_of_margin`, `thmKUpper_of_margin`, `thmK_of_margin`, `mainTheorem_shear_of_margin`: the source's `ThmK`/`ThmN`, unrestated | [COND: `AngularMargin` / `PositionMargin`] |
| T3 leading + remainder | `SLT/Template/Leading`: a nondegenerate leading part discharges `AngularMargin`, giving pair `(D/(2d), 1)` | residual-slt's `positive_homogeneous_laplace_order` re-derived (zero remainder) | [LC] |
| T4 read/write block | (core N2 only) | one block `u v³`: crossing and read-dead `(1/6,1)`, write-dead `(1/2,1)` | [LC] |

- **Counts.** Core 243 → 286 audited; zoo 25 → 76, plus 11 source theorems re-checked.
- **Routing for new architectures.**
  - Nondegenerate weighted-homogeneous leading map: T3, all hypotheses checkable.
  - Loss comparable to a monomial sum: N2.
  - Degenerate leading map: T2 with `AngularMargin` as a named hypothesis. It needs Phong–Sturm stability plus
    a real transfer (the project plan, kept outside this repository).
- **Open items.**
  - The real transfer has to be uniform in `r` (design risk; see the project plan, kept outside this repository).
  - The (K3) construction for `PositionMargin` is costed at 600–1000 lines per position.
  - Quasi-homogeneous T3 is unbuilt, with no consumer.
  - The two-block identity group is [unverified] at `(1/3, 1)`.
  - M3 stays on hold.

## Brief 04, T5: MLP arrangement ideals at model level (2026-11-08)

**Branch `t5-mlp-ideals`**, cut from `main` @ `21387ba`. It is not merged and not pushed. Bobby approved T5
only ("Approve T5"); this does not cover (K3) or M3.

**File:** `zoo/Zoo/MLPArrangement.lean`. **No core change.** It uses N2 (`newton_box_units`) and M1
(`HasLaplacePair.prod`) as they are. The file adds zoo-level helpers:
- `powΓ`, with `newtonDist_powΓ`, `optWeights_powΓ`, `pair_of_powΓ`: pure-power exponent sets give
  `(Σ 1/kᵢ, 1)`;
- `pair_of_Γ` and `newtonMult_eq_two`;
- `regular_add_pair`: regular `(n/2, 1)` ⊕ residual.

**[LC] at model level.** The chart reductions (eliminating regular coordinates) are paper-proved in resnet-bridge,
AI-reviewed, and not formalized.

| Source | Lean | Pair |
|---|---|---|
| S2′ (in, out), `J = (a, c)` | `s2p_inOut` (via `spare_inOut_pair`) | `(5/2, 1)` |
| S2′ (out, in), `J = (B, q, r)` | `s2p_outIn` | `(3, 1)` |
| S2′ (in, both), `J = (a, cq)` | `s2p_inBoth` | `(5/2, 2)` |
| S2′ (both, in), `J = (q) + a(B, r)` | `s2p_bothIn` | `(5/2, 1)` |
| S2′ (both, out), `J = (aB, c)` | `s2p_bothOut` | `(5/2, 2)` |
| S2′ (out, both), `J = (B) + c(q, r)` | `s2p_outBoth` | `(5/2, 1)` |
| S2″ M1, M4, `(ε²)` | `m1_m4_pair` | `(9/4, 1)` |
| S2″ M2, `(w, p)²` | `m2_pair` | `(5/2, 1)` |
| S2″ M3 (slice `ρ = 0`), `(ε², ρε)` | `m3_pair` | `(5/2, 2)` |
| S2″ M3′ (`ρ* ≠ 0`), the same ideal at `(0, ρ*)` | `m3'_pair` | `(5/2, 1)` |
| hunt T4 (dup, dup), `(g, ε)²` | `dupDup_pair` | `(2, 1)` |
| headline: (out, in) vs (in, out) | `outIn_ne_inOut` (includes `¬ HasLaplacePair … (5/2) 1` at (out, in), via `unique`) | `(3,1)` vs `(5/2,1)` |
| headline: M4 vs M3′ | `m4_ne_m3'` | `(9/4,1)` vs `(5/2,1)` |

- **S2′ is stronger than the forum's transcription.** All six arrangements are points of **one** loss,
  `(aB)² + (cq)² + (car)²`, on the five spare weights. The live weights are nonzero parameters and the units are
  handled in Lean. So the localization step ("which edges must be cut") is also certified, not just the localized
  ideals.
- **Transcription check.** Every ideal and pair in `bridge_brief_04.md` matches the sources, and **the Lean agrees
  with every pair**. One note: at (in, out) and (in, both), `r` is free and needs no nonzero hypothesis.
- **Not done.**
  - S2′ (both, both) `(5/2, 3)`. Its Newton data has a 2-dimensional optimal face. The source rates `m = 3` as
    "plausible" only numerically, so certifying it would upgrade that rating. It would cost about 60 lines.
  - (in, in) and (out, out).
  - The hunt's special point T4s, and rows T1, T1b, T1c, T3.
- **R0.2** (`docs/T5_R02_note.md`). It is **not** Newton-degenerate in the relevant sense. It is
  non-monomial in `(w, y)`, but after the triangular unit-Jacobian shear `y₁ ↦ S` (the paper's own step)
  `K ≍ S² + Σw¹² + Σ_{j≥2} y⁴`, which is pure-power and gives `J(p, q)` exactly. One wording fix for the source:
  that shear is not linear. A Lean certificate is about 150 lines for `J(1,1)`; it is not built and needs Bobby's
  OK.
- **Audit.** Core 286/286 (unchanged). Zoo 165 public declarations plus 11 source theorems, 176/176, all on
  `[propext, Classical.choice, Quot.sound]`. No `sorry`. The Batteries lint is clean and the new file has zero
  warnings.

### T5 cleanup (2026-11-08, Bobby's request before the merge)

- **Sources pinned.** The docstrings and READMEs now name the resnet-bridge commits the Lean was matched against:
  `4a7060c` for S2′ and S2″, `f23016c` for the hunt, and `c55350b` for R0.2. resnet-bridge HEAD was `e96f766`, and
  these are the last commits that touched each file.
- **Labels.** The `MLPArrangement` header now has a "What is not certified here" paragraph, and the README rows say
  "[LC] for the model losses only". The network-to-model chart lemma is paper-proved and AI-reviewed, not
  Lean-certified. Its rank condition is a Python check, and its exceptional set is not shown to be complete.
- **`m4_ne_m3'`.** The docstring now says it compares two different functions in two coordinate systems. The claim
  that they share one parameter space at equal codimension rests on the source; `outIn_ne_inOut` does not have
  this caveat.
- **Duplicates removed.**
  - The MLP file's `Z_translate` copy and `newtonMult_eq_one` are gone. It now imports `Zoo.ReadWrite` and uses
    `Z_translate`, `withDensity_one_box` and `newtonMult_eq_one_of_singleton`.
  - `newtonMult_eq_one_of_singleton` is generalized from `Fin 2` to any `Fin d`. This is non-breaking: `d` is
    implicit.
- **19 file-local helpers made private**, following the brief 02 precedent. These are box and unit bounds, the
  `Γ…_nonneg` lemmas, `spareLoss_add`, and so on. Zoo public declarations drop 165 → 144.
- **Not moved to the core:** the general Newton helpers `powΓ`, `pair_of_powΓ`, `pair_of_Γ`, `newtonMult_eq_two`
  and `regular_add_pair`. Moving them would be a core change outside T5. They are a candidate for a later core pass.

### S2′ (both, both) (2026-11-08, Bobby's go-ahead)

Branch `mlp-both-both`, cut from `main` @ `8b050b0`. (`main` had already been fast-forwarded to `8b050b0` from
`t5-mlp-ideals` at 09:24, before this request.)

- **`s2p_bothBoth`: total `(5/2, 3)`.** At the all-zero spare point, `K_J` is the whole spare loss,
  `Γ = {2e_a + 2e_B, 2e_q + 2e_c, 2e_a + 2e_r + 2e_c}`, with `t* = 1`.
- **The optimal face is a triangle**: `u_r = 0`, `u_a + u_B = u_q + u_c = 1/2`, `u_a + u_c ≥ 1/2`
  (`optWeights_bothBoth`). Its three vertices are affinely independent (`affineIndependent_bothBothVertex`), so
  `m = dim O + 1 = 3`.
- **This is the first `m = 3` in the zoo.** The source's toy integral rated it only "plausible" (slowly drifting
  second differences). It is now [LC] at model level, with the same chart-lemma caveat as the rest of T5.
- **New general lemma:** `convex_optWeights`.

### R0.2 certificate, `J(1, 1) = (7/12, 1)` (2026-11-08, Bobby's go-ahead)

Branch `r02-certificate`, cut from `main` @ `fd0b247`. **File:** `zoo/Zoo/MixedGroup.lean`. **No core change.**

- **[LC] `mixedGroup_pair`.** The loss `(w³ + y)² + (w⁶ + y²)²` has pair `(7/12, 1)` on every box `[-δ, δ]²`
  with `0 < δ ≤ 1/2`. `mixedGroup_pair_formula` restates it in the source's `J(p, q)` form.
- **Route.** In `(w, y)` the loss is not monomial-comparable (`docs/T5_R02_note.md` §1).
  - The shear `y = s − w³` preserves measure (`measurePreserving_shear`, via the Mathlib skew product).
  - The shear's preimage of the box lies between two boxes.
  - On those boxes `shearLoss ≍ w¹² + s²`, so N2 gives the pair, and the original box gets it by
    `HasLaplacePair.squeeze`.
- **This confirms the source's pair**, including `m = 1`, which `R0_scalar.md` says it did not check
  numerically ("Lemma R0.2's m = 1 is proved by quasi-homogeneity").
- **Not built.** General `(p, q)`, which needs `Fin.append` bookkeeping only. Also the "linear" wording fix in the
  source, which is not ours to edit.
- **Audit.** Core 286/286. Zoo 169 public declarations plus 11 source theorems, 180/180, all on
  `[propext, Classical.choice, Quot.sound]`. Lint clean, zero warnings.

### The position table from three inactive Laplace bounds (2026-11-10, Papers forum, Bobby's go-ahead)

Branch `loss-glue`, cut from `main` @ `e032936`. **File:** `zoo/Zoo/LossComparison.lean`. **No core change.**
The zoo's VectorSLT pin moves to `196b8df` (`VectorSLT/LossCompare` was added at `7ac38c6`; `196b8df` changes
only its documentation).

- **What changed upstream.** `vector-slt-lean` now proves the loss comparison at positions two to four for every
  shear target: coordinates `(𝐜, w)` with a bounded change of variables, `κ (‖𝐜‖² + G_p(w)) ≤ K`, and
  `G_p(r ξ) = r⁶ H_p(r, ξ)` for explicit polynomials. That is `PositionMargin` without the angular margin.
- **[COND: `InactiveLaplace`] `mainTheorem_shear_of_inactiveLaplace`.** The table `(4,5), (4,1), (4,1), (4,1)` from
  `InactiveLaplace (Gmid 1)`, `InactiveLaplace (Gmid 2)`, `InactiveLaplace G4`: on some ball of `ℝ¹²`,
  `∫ e^{-N G_p} ≤ C N⁻²`. The hypotheses mention no network, target, input law, prior or cutoff.
  `thmN_of_inactiveLaplace` and `thmKUpper_of_inactiveLaplace` give the source's two named hypotheses.
- **Why this hypothesis and not the angular margin.** The first version of this file (`ccca232`) was conditional
  on `ShellMargin H_p`, the template's `AngularMargin` for the explicit angular parts. That is a real bound,
  uniform in the radius `r`. Paper 2 does not prove it. Its analytic step works over `ℂ`: the stability theorem
  of Phong and Sturm gives a uniform complex margin, hence `N⁻⁴` for the integral over a polydisk of `ℂ¹²`, and
  a transfer through a real resolution of singularities turns that Laplace bound into `N⁻²` over `ℝ¹²`. What
  it delivers is `InactiveLaplace`. `ShellMargin` implies it (`inactiveLaplace_of_angularMargin`,
  `mainTheorem_shear_of_shellMargin`) and stays in the file as a sufficient condition. Note for M3: discharging
  `AngularMargin` itself from a complex threshold bound would need a real stability statement that the two
  cited theorems do not supply; `InactiveLaplace` needs only what they state.
- **[LC] `H4_zero_eq_core`, `Hmid_one_zero_eq_core`, `Hmid_two_zero_eq_core`.** At `r = 0`, `H_p` is the squared
  norm of the core's complex leading map at the real point.
- **Not built.** The inactive bounds themselves.
- **Audit.** Core 797/797. Zoo 205 public declarations plus 16 source theorems, 221/221, all on
  `[propext, Classical.choice, Quot.sound]`. Lint clean.
