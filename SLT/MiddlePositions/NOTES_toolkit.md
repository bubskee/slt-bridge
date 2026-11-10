# Middle positions, toolkit (note §2 and §6): working notes

Branch `mid-toolkit`. Source: `forum/complex_middle_positions/complex_middle_positions.tex`
(2026-11-09), §2 ("Elementary planar estimates and weighted two-cube input") and §6 ("A shell
corollary without polar coordinates").

## Status

All three interface statements of `SLT/MiddlePositions/Defs.lean` are **proved**, with no
hypotheses:

```lean
theorem toolkit_weightedTwoCubeBound : ∃ C, WeightedTwoCubeBound C          -- C = 16/9
theorem toolkit_locallyIntegrableF : LocallyIntegrableF
theorem toolkit_fullPlaneQuadratic : ∀ t : ℝ, 1 < t → t < 2 → ∃ C, FullPlaneQuadratic t C
```

Explicit constants: `weightedTwoCubeBound_sixteen_ninths : WeightedTwoCubeBound (16 / 9)` and
`fullPlaneQuadratic_quadC : FullPlaneQuadratic t (quadC t)` with
`quadC t = 4^{t-1} (K_t + 1)`, `K_t = ∫_ℂ |z² - 1|^{-t}` (`quadConstT`).

Stretch item (note §6), also proved:

```lean
theorem toolkit_shell_two (h : SublevelTwo) {s : ℝ} (hs : s < 97 / 24) :
    ∫⁻ w in homShell (Row2 × Row2), ‖R2 w‖ₑ⁻¹ ^ (2 * s) < ⊤
theorem toolkit_shell_three (h : SublevelThree) {s : ℝ} (hs : s < 97 / 24) :
    ∫⁻ w in homShell (Row3 × Row3), ‖R3 w‖ₑ⁻¹ ^ (2 * s) < ⊤
```

* Build: `lake build SLT.MiddlePositions.Toolkit`. Zero warnings after a clean rebuild of the
  toolkit modules.
* Audit: `lake env lean SLT/MiddlePositions/AuditToolkit.lean`. 72/72 public declarations (list
  generated with `scripts/DumpDecls.lean`, prefix `SLT.MiddlePositions.Toolkit`), all on
  `[propext, Classical.choice, Quot.sound]`.
* Batteries `#lint in SLT.MiddlePositions` and `#lint only docBlameThm in SLT.MiddlePositions`
  (with the toolkit imported): no errors (85 declarations, `Defs.lean` included).
* No `sorry`, `admit` or `native_decide`. No existing file edited; `Defs.lean` committed unchanged.

## Modules

| Module | Content |
|---|---|
| `Toolkit/Quadratic` | `K_t < ∞`; the exact full-plane integral `lintegral_quadratic_eq_rpow`; Interface 3; the shifted disc at exponent `p ∈ (0, 2)` |
| `Toolkit/Weighted` | `‖H(P)‖ ≤ 2‖P‖²`, `‖g‖ |det g| ≤ 4‖Ψ(g)‖`, the weight bound, the multiplier `twoCubeWeight`; Interface 1 |
| `Toolkit/Local` | `discDensity t = |𝔇|^{-t}`; the `P₃`, `P₂` integrals; cone chart; balls for `1 < t ≤ 3/2`; Interface 2 |
| `Toolkit/Shell` | the shell bound for any continuous cubically homogeneous map; `R2`, `R3` homogeneity and continuity; `shell_two`, `shell_three` |
| `Toolkit` (root) | imports the four, restates the headline theorems |

## Note versus Lean

### Lemma "Planar powers and quadratics"

| Note | Lean |
|---|---|
| item 1, shifted disc `∫_{D_R} |z - c|^{-t} ≤ A_t R^{2-t}` | `lintegral_closedBall_rpow_sub_le_rpow` (for `0 < p < 2`; constant `discConstP p`) |
| item 1, centered disc / tails | from `SLT.PositionFour.lintegral_ball_rpow_neg_lt_top` (existing) |
| item 2, `∫ |z² - 1|^{-t} < ∞` (`γ = 0`) | `quadConstT_lt_top`, via the existing `lintegral_twoPoint_lt_top` |
| affine substitution `z = c + d u`, choice `c = -B/2A`, `d² = Δ/4A²` | inside `lintegral_quadratic_eq_rpow` (an equality, any real `t`) |
| last display `∫ |q|^{-t} ≤ C_t |A|^{t-2} |Δ|^{1-t}` | `fullPlaneQuadratic_quadC`, `fullPlaneQuadratic` |

### Lemma "Weighted two-cube measure bound", first half

| Note | Lean |
|---|---|
| norm dichotomy and `𝔇(Ψ(g)) = (det g)⁶` | existing `norm_twoCube_cases`, `disc_twoCube` |
| `‖H‖ ≤ 2‖P‖²` | `norm_hess_le` |
| `W₂(g) ≤ C(1 + ‖P‖^β |𝔇(P)|^{-β/6})` | `W2_le_of_det2_ne_zero` (`C = 8`), as `ofReal_W2_le` in `ℝ≥0∞` |
| multiply into `twoCubeBound` | `lintegral_W2_twoCube_le` (via the existing `lintegral_twoCube_le`), `twoCubeWeight_mul_le` (`4/3 + 1/24 = 11/8`) |
| measure inequality | `weightedTwoCubeBound_sixteen_ninths` |

### Same lemma, second half (local finiteness)

| Note | Lean |
|---|---|
| region `|P₀| ≤ M`, `|Pᵢ| ≤ K|P₀|` | existing `chart C R = {‖P‖ ≤ R, ‖P‖ ≤ C|P₀|}` |
| `P₃` over `ℂ`, discriminant `16 (P₁² - P₀P₂)³` | `lintegral_last_le_rpow` (existing `disc_eq_quadratic`, `discr_disc`) |
| `P₂` shifted disc, `|P₀|^{2-2v}`, `v = 3t - 3` | `lintegral_middle_le_rpow` |
| `P₁` disc `|P₀|²`, then `|P₀|^{6-4t}` | `enorm_rpow_mul_ofReal_mul_sq_le`, `lintegral_chart_discDensity_lt_top` |
| four substitutions, `‖P‖ ≤ max` of four evaluations | existing `chartPair`, `exists_chart`, `lintegral_comp_cubicAct`; new `discDensity_cubicAct_of_norm` |
| `∫_{‖P‖ ≤ R} |𝔇|^{-t} < ∞` | `lintegral_closedBall_discDensity_lt_top` |
| bound `‖P‖^β ≤ R^β`, then (localF) | `locallyIntegrableF` (the `4/3` summand by the existing `lintegral_closedBall_twoCubeDensity_lt_top`) |

### §6, shell corollary

| Note | Lean |
|---|---|
| `E_k`, scaling by `2^{k-1}`, `vol(E_k) ≤ C I 2^{-k(24+β)}` | `homLayer`, `homLayer_volume_le` |
| sum over layers, `s < 97/24` | `lintegral_homShell_lt_top_of_moment` (general), `_24`, `shell_two`, `shell_three` |

## Departures from the note

1. **Weight bound, shorter route.** Both cases of `norm_twoCube_cases` give the single inequality
   `‖g‖ |det g| ≤ 4 ‖Ψ(g)‖` (`norm_mul_norm_det2_le`): in case 1 use `|det g| ≤ 2‖g‖²`, in case 2
   use `‖H‖ ≤ 2‖P‖²`. Hence `‖g‖^{1/4} ≤ 2 ‖P‖^{1/4} |𝔇|^{-1/24}` directly. The intermediate term
   `‖P‖^{β/3}` and the bound `|𝔇(P)| ≤ 18 ‖P‖⁴` are not needed (both are correct; I checked the
   coefficient sum `1 + 6 + 4 + 4 + 3 = 18`).
2. **Local finiteness: finiteness only, `t ≤ 3/2`.** The explicit growth `C (R^{8/3} + R^{11/4})`
   of (localF) is not formalized; the interface asks only for finiteness. The ball lemma is stated
   for `1 < t ≤ 3/2` (so `6 - 4t ≥ 0` and the last integrand is bounded on `|P₀| ≤ R`) instead of
   the note's `3t - 3 < 2`, `6 - 4t > -2`; this covers the two exponents `4/3` and `11/8`. The chart
   constants are `‖L_j‖ + 1` (operator norms, as in `Upstream/Local.lean`) instead of the note's
   explicit `K = 8`, `M = 8R`. (The note's operator-norm claim `≤ 8` is right in the sup norm:
   for `t ↦ s + t` the new coefficients are `P₀ + 3P₁ + 3P₂ + P₃`, `P₁ + 2P₂ + P₃`, `P₂ + P₃`, `P₃`.)
3. **Not formalized from Lemma "Planar powers and quadratics":** item 2 with `γ > 0` and the
   weighted display (quadw), and the tail bound `∫_{|z|>R} |z|^{-t} ≤ B_t R^{2-t}`. They are not
   part of the interface. If `mid-two` / `mid-three` need (quadw), it has to be added.
4. **Interface 3 at `Δ = 0`.** The interface includes the case `B² = 4AD`, where its right side is
   `∞`; this needs `C > 0`, which is why the constant is `4^{t-1}(K_t + 1)` rather than
   `4^{t-1} K_t`.
5. **Shell lemma generality.** The map is `R : E → V` into any normed group, continuous (the note's
   "bounded on the unit ball" is derived from continuity and compactness), with
   `‖R (c • w)‖ = c³ ‖R w‖` for real `c > 0`; `E` is any finite-dimensional real normed space with
   an additive Haar measure `μ` and `finrank ℝ E = n`; the condition is `6s < n + β`
   (`lintegral_homShell_lt_top_of_moment_24`: `2s < 8 + β/3` for `n = 24`).

## How to apply the shell lemma

For a map `R` on `X = Row2 × Row2` or `Row3 × Row3` (or any other product of `ℂ`'s):

1. homogeneity: `R2_smul`/`R3_smul` give `R (c • w) = c³ • R w`, hence `norm_R2_smul`;
2. continuity: `continuous_R2` / `continuous_R3`;
3. dimension: `finrank_row2Pair` / `finrank_row3Pair` (`= 24`, by
   `simp [Module.finrank_prod, Complex.finrank_real_complex]`);
4. Haar measure: the instances `isAddHaarMeasure_volume_row2Pair` / `_row3Pair` (and the
   `BorelSpace` instances `borelSpace_row2Pair` / `_row3Pair`, which instance search did not find
   on its own for these nested products);
5. `lintegral_homShell_lt_top_of_moment_24 volume continuous_R2 (fun _ hc w => norm_R2_smul hc w)
   finrank_row2Pair (β := 1/4) (by norm_num) hs h`, with `h : SublevelTwo`.

`shell_two` and `shell_three` are exactly this. The shell is `homShell X = {1/2 ≤ ‖w‖ < 1}` (sup
norm), the same set as `SLT.PositionFour.Downstream.rowShell` on `Row × Row`.

## Merge notes

* New public names live in `SLT.MiddlePositions` and do not clash with `SLT.PositionFour`. The
  instances `borelSpace_*` and `isAddHaarMeasure_volume_*` in `Toolkit/Shell.lean` are named
  instances; if `mid-two` or `mid-three` declare instances under the same names, rename one side.
* Reusable lemmas for the sibling branches: `lintegral_quadratic_eq_rpow` (exact formula, any `t`),
  `lintegral_closedBall_rpow_sub_le_rpow` (shifted disc), `lintegral_closedBall_discDensity_lt_top`,
  `lintegral_W2_twoCube_le` (integral form of Interface 1).

## Errors or gaps in the note's §2

None found. Every displayed inequality of §2 was checked: the scaling `|A|^{-t} |d|^{2-2t} =
4^{t-1} |A|^{t-2} |Δ|^{1-t}`, the discriminant `16 (P₁² - P₀P₂)³`, the exponent bookkeeping
`2t - 4 + (2 - 2v) + 2 = 6 - 4t` and `4/3 + 1/24 = 11/8`, the covering identities
`6P₁ = P(1,1) - P(1,-1) - 2P₃`, `6P₂ = P(1,1) + P(1,-1) - 2P₀`, and the §6 exponent
`6s < 24 + 1/4 ⇔ s < 97/24`. The only imprecision is cosmetic: the "Consequently" of item 2 needs
`γ ≥ 0` for `|c + du|^γ ≤ C_γ(|c|^γ + |d|^γ |u|^γ)`, which the hypothesis `0 ≤ γ` provides.
