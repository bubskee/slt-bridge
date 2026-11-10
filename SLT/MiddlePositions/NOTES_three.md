# Position three: working notes (`mid-three`)

> Historical working note of the session that wrote this code. Since the consolidation, some
> files and declarations have moved to `SLT/Pushforward` or been merged, and the per-directory
> audit files are replaced by the root `Audit.lean`. Current locations and the list of removed
> or renamed declarations: `SLT/Pushforward/NOTES.md`.

Source: `forum/complex_middle_positions/complex_middle_positions.tex` (2026-11-09), Theorem
"Position three". Branch `mid-three`, cut from `c4-position-four`. Lean v4.35.0, mathlib `56a0058`.

## Status

**Proved:** `SLT.MiddlePositions.Three.sublevelThree`
(`SLT/MiddlePositions/Three.lean`):

```lean
theorem sublevelThree {C : ℝ} (hW : WeightedTwoCubeBound C) (hF : LocallyIntegrableF)
    (hQ : ∀ t : ℝ, 1 < t → t < 2 → ∃ K, FullPlaneQuadratic t K) : SublevelThree
```

The only open hypotheses are the three interface statements of `SLT/MiddlePositions/Defs.lean`
(proved on `mid-toolkit`). `Defs.lean` is unchanged (first commit `fee8a63`). `FullPlaneQuadratic`
is used at `t = 4/3` and `t = 11/8` only. `LocallyIntegrableF` is used once, at radius `64`.
`WeightedTwoCubeBound` is used in its measure form, once in each prefix row.

**Audit:** `lake env lean SLT/MiddlePositions/AuditThree.lean` gives 96/96 public declarations
depending on exactly `[propext, Classical.choice, Quot.sound]`. There is no `sorry`, `admit`,
`native_decide`, new axiom or `maxHeartbeats` override. `lake build SLT.MiddlePositions.Three` gives
zero warnings under the repository linters.

**No error found in the note.** Every step of the position-three proof went through, sometimes in a
cruder form (see Departures). The interface is strong enough as stated.

## Files

| file | content |
|---|---|
| `Three/Suffix.lean` | Lemma "Weighted one-form suffix": `kernelN3`, pushforward identity, bounds, `L¹`/`L²` |
| `Three/Marginal.lean` | Lemma "Pointwise bounds on explicit regions": `marginal`, outer/central bounds, near `L¹`, far `L²` |
| `Three/Prefix.lean` | Lemma "Uniform translated prefix bound": abstract kernel bound, `prefix_bound` |
| `Three/Assembly.lean` | Proof of Theorem "Position three" |
| `Three.lean` | root: imports, restates `sublevelThree` |
| `AuditThree.lean` | one `#print axioms` per public declaration |

## Note versus Lean

| note | Lean |
|---|---|
| `F = |𝔇|^{-4/3} + ‖P‖^{1/4}|𝔇|^{-11/8}` | `Defs.F`; `F_eq` (form with `‖𝔇‖ₑ⁻¹ ^ t`), `measurable_F` |
| Lemma suf1, substitution `b = Q/a²` | `lintegral_suffixWeight_mul` (an identity of `lintegral`s, in form coordinates) |
| `N₃` | `kernelN3 Q = ∫ W₁(a, Q/a²) 𝟙_suf(a, Q/a²) |a|^{-4} da` |
| constraints `|ab²| < 1`, `|b|³ < 1` force `|a| > A(Q)` | `suffix_lower`, `kernelN3_le_of_threshold` |
| (eq:n3): `N₃ ≤ C|Q|^{-1}` / `C|Q|^{-7/6}` | `kernelN3_le_small` / `kernelN3_le_large`, with `C = 3π` |
| `m(U,V) = ∫_{D₁²} F` | `marginal` (sup norm ball on `(P₂, P₃)`) |
| outer region `𝒪 = {y ≥ 16, x ≤ y^{3/2}/16}`, `m ≤ C y^{-15/4}` | `marginal_le_outer` on `{16 ≤ y, 256x² ≤ y³}` (the same set) |
| one-dominant-root step, `|B| ≥ 3y³`, `8|A| ≤ |B|` | `discInt_le_outer`, via `Downstream.lintegral_ball_one_inv_quadratic_le` |
| complement: `x ≥ 1`, `y ≤ (16x)^{2/3}`, `‖P‖ ≤ Cx`, `m ≤ C x^{-17/8}` | `marginal_le_central` on `{x ≥ 1, y ≤ 16x}`; case split in `marginal_sq_le_far` |
| full-plane quadratic in `v`, then shifted disc in `u` | `discInt_le_central`: `FullPlaneQuadratic` plus `Downstream.lintegral_ball_inv_delta_le` |
| `f = m 𝟙{‖λ‖<64} ∈ L¹` | `lintegral_marginal_near_lt_top` (`∫_{‖λ‖<64} m ≤ ∫_{‖P‖≤64} F`) |
| `g = m 𝟙{‖λ‖≥64} ∈ L²` | `lintegral_marginal_far_sq_lt_top` |
| Lemma pref2, `∬ K(λ-μ-z) m m ≤ B` uniformly in `z` | `lintegral_kernel_le` (abstract), `marginal_kernel_bound` |
| `P₃(c) ≤ CB` | `prefix_bound` (bound `C² B`, uniform in `c`) |
| product weight `≥ ‖w‖^{1/4}` | `rpow_norm_le_weight` |
| "Tonelli gives `C ∬_{|Q₁-Q₂|<1} N₃N₃P₃(-Q₁)`" | `sublevel_indicator_le`, `measurePreserving_shuffle`, the `calc` in `sublevelThree_of_interface` |
| Lemma average with `κ = 1`, `ν = 7/6`, `γ = 0` | replaced: `suffix_bound` (see Departures 5) |

Sign conventions match the note. The prefix kernel `prefixKernel c` encodes
`|P¹₀ - P²₀ + c| < 1`, `|P¹₁ - P²₁| < 1`, so the translation is `z = (-c, 0)` and the assembly
uses `c = Q₁ = q¹₁`. This is the note's `P₃(-Q₁)` with its constraint `|p¹₀ - p²₀ - c| < 1`.

## Departures from the note

1. **`N₃` is not computed exactly.** `kernelN3` is defined as the integral over `a` that the
   substitution produces. The pushforward statement is an exact identity of `lintegral`s.
   The closed form (eq:n3exact) is not formalized. Instead, an upper bound by the three planar
   tails over `|a| > c` is proved. The threshold `c` is `|Q|^{1/2}` for `|Q| ≤ 1` and `|Q|^{2/3}`
   for `|Q| ≥ 1`, i.e. only the binding half of `A(Q) = max(...)` in each regime. This gives
   `N₃ ≤ 3π|Q|^{-1}` and `N₃ ≤ 3π|Q|^{-7/6}`. The exact constants `π + 8π/7 + 4π/5 = 103π/35`
   are below `3π`.
2. **Regions in Lemma pref2tail.** The outer region is written polynomially,
   `256 x² ≤ y³` (`⟺ x ≤ y^{3/2}/16`). The central bound is proved on the larger set
   `{x ≥ 1, y ≤ 16x}`, and the complement of `𝒪` in `{max(x, y) ≥ 64}` is shown to lie in it.
   The square integrals use the enlarged sets `{y ≥ 16, x ≤ y²}` and `{x ≥ 1, y ≤ 16x}`. They
   reduce to the planar tails `∫_{|V|>8} |V|^{-7/2}` and `∫_{|U|>1/2} |U|^{-9/4}`. In the note's
   radial form these are `y^{-5/2} dy` and `x^{-5/4} dx`, against the note's `y^{-7/2}` and
   `x^{-23/12}`. Less slack, but still finite. No fractional radii are needed.
3. **The `ε`-free weight bound.** On the outer region `‖P‖² ≤ y³`, hence `‖P‖^{1/4} ≤ y^{3/8}`.
   On the central region `‖P‖ ≤ 16x`. These are the note's `‖P‖ ≤ C y^{3/2}`, `‖P‖ ≤ Cx` with
   explicit constants.
4. **The translated bound without Cauchy–Schwarz.** `lintegral_kernel_le` is proved for every
   finite-dimensional real normed space with an additive Haar measure. It assumes only `m ≤ f + g`
   with `∫ f < ∞` and `∫ g² < ∞`. The mixed and `gg` terms are bounded by `a ≤ 1 + a²` and
   `ab ≤ a² + b²` plus translation invariance of the unit ball's volume, not by Cauchy–Schwarz. The
   bound is `‖f‖₁(‖f‖₁ + V + ‖g‖₂²) + ‖g‖₂²(‖f‖₁ + V) + V(‖f‖₁ + ‖g‖₂²)`, with `V = |B₁|`. It is
   independent of `z` and finite. The near part `f` is never squared.
5. **No local-averaging lemma.** The note ends with Lemma "Local averaging of a planar bound". Here
   the suffix double integral `∬_{|Q₁-Q₂|<1} N₃(Q₁) N₃(Q₂)` is bounded by the same
   `lintegral_kernel_le`, now on `ℂ` with `z = 0`. The split is
   `N₃ = N₃ 𝟙{|Q| ≤ 1} + N₃ 𝟙{|Q| > 1}`: the first part is in `L¹` because `κ = 1 < 2`, the second
   in `L²` because `2ν = 7/3 > 2`. `P₃` enters only through its uniform bound, i.e. `γ = 0`. The
   exponent conditions are the same as the note's (`κ < 2`, `2ν + γ > 2`).
6. **Tonelli.** The note's "Tonelli gives" is a measure-preserving reshuffle
   `((g₁, l₁), (g₂, l₂)) ↦ ((g₁, g₂), (l₁, l₂))` (`measurePreserving_shuffle`, built from
   `prodAssoc`, `swap` and `Prod.map`). It is followed by `lintegral_prod_symm`: the prefix pairs
   are integrated first, for fixed suffix forms.
7. **Interface constants.** `FullPlaneQuadratic t K` is used with `max K 0`
   (`fullPlaneQuadratic_mono`). This allows a possibly negative `K` and keeps all `ofReal`
   manipulations sign-safe.
8. **Product weight.** `rpow_norm_le_weight` proves `‖w‖ ≤ (W₂W₂W₁W₁)⁴` entry by entry (sup norm)
   and takes fourth roots. This is the note's "the factor belonging to a largest entry".

## Reused `PositionFour` code (read only)

`Downstream.toCubic`, `disc_toCubic`, `discr_disc`, `setLIntegral_ball_prod`,
`lintegral_ball_inv_delta_le`, `ballConst`, `lintegral_cubic`, `measurable_toCubic`
(`Marginal`, `Finiteness`); `lintegral_ball_one_inv_quadratic_le`, `enorm_inv_rpow_of_ne_zero`,
`enorm_mul_inv_rpow`, `enorm_pow_inv_rpow` (`Quadratic`); `lintegral_ball_inv_rpow`,
`lintegral_norm_gt_inv_rpow` (`Radial`); `lintegral_comp_mul_left` (`Upstream/Coords`);
`twoCube`, `twoCubeDensity` (`Upstream`).

## Not formalized here

The closed form of `N₃`; Theorem "Position two" (on `mid-two`); the interface lemmas
(`mid-toolkit`); the dyadic shell corollary of the note's Section 7; the note's sharpness remarks.

## Lean-side notes

* Instance search does not find `SigmaFinite (volume : Measure ((Form × Form) × (Form × Form)))`
  within default limits. `sigmaFinite_volume_prefixPairs` supplies it, as a theorem rather than a
  global instance.
* Composing `Measurable.comp` with a lemma about `ball p.1 1` on a product timed out in `whnf`.
  The measurability lemmas therefore take measurably moving arguments directly
  (`measurable_indicator_ball_comp`, `measurable_prefixKernel_comp`).
* Namespace `SLT.MiddlePositions.Three` throughout. Nothing is added to `SLT.lean` or
  `Audit.lean`.
