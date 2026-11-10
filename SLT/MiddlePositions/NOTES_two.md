# Middle positions: position two (working notes)

> Historical working note of the session that wrote this code. Since the consolidation, some
> files and declarations have moved to `SLT/Pushforward` or been merged, and the per-directory
> audit files are replaced by the root `Audit.lean`. Current locations and the list of removed
> or renamed declarations: `SLT/Pushforward/NOTES.md`.

Branch `mid-two`, worktree `slt-bridge-mid2`, cut from `c4-position-four`. This is Theorem
"Position two" of `forum/complex_middle_positions/complex_middle_positions.tex` (2026-11-09). It
assumes the interface of `SLT/MiddlePositions/Defs.lean`, which is unchanged and shared with
`mid-toolkit` and `mid-three`.

Build: `lake build SLT.MiddlePositions.Two`, with zero warnings.
Audit: `lake env lean SLT/MiddlePositions/AuditTwo.lean`. It has 77 lines, one per public
declaration of `SLT/MiddlePositions/Two.lean` and `SLT/MiddlePositions/Two/`. All 77 report
`[propext, Classical.choice, Quot.sound]`. The Batteries linters (`#lint`, and `#lint only
docBlameThm`) find 0 errors in `SLT.MiddlePositions.Two`. There is no `sorry`, `admit`,
`native_decide` or `axiom`.

All declarations are in the namespace `SLT.MiddlePositions.Two`.

## Result

```lean
theorem SLT.MiddlePositions.Two.sublevelTwo {C : ℝ} (hW : WeightedTwoCubeBound C)
    (hQ : ∀ t : ℝ, 1 < t → t < 2 → ∃ K, FullPlaneQuadratic t K) : SublevelTwo
```

The interface use is as follows.

* `WeightedTwoCubeBound C` is applied once to each suffix row, through `lintegral_W2_le`.
* `FullPlaneQuadratic t K` is used only at `t = 9/8`, `4/3` and `11/8`.
* **`LocallyIntegrableF` is not used.**
* No stronger form of any interface statement is needed.

The explicit form is `sublevel_two_le`:
`∫_{‖R₂‖<1} ‖w‖^{1/4} ≤ (C · Msuf)² · ∫∫ V 𝟙_{preSet}`, and the last factor is finite
(`lintegral_pre_lt_top`).

## Note versus Lean

| Note | Lean | File |
|---|---|---|
| Planar powers and quadratics (1), shifted disc | `setLIntegral_ball_inv_rpow_le`, `…_three_pi` (via `Downstream.lintegral_ball_sub_inv_rpow_le`) | `Two/Planar.lean` |
| Planar powers and quadratics (1), tail powers | `Downstream.lintegral_norm_gt_inv_rpow` (reused), `lintegral_max_one_rpow_neg_lt_top` | `Two/Planar.lean` |
| Planar powers and quadratics (2), `eq:quad0` | `lintegral_inv_quadratic_le` (read off `FullPlaneQuadratic`) | `Two/Planar.lean` |
| Planar powers and quadratics (2), `eq:quadw` | `lintegral_rpow_mul_inv_quadratic_le` (`0 ≤ γ ≤ 1`, `γ < 2t-2`) | `Two/Planar.lean` |
| An explicit two-variable integral (`J_{a,t}`), the `L_t` bounds | `L`, `L_le`, `rpow_mul_L_le` | `Two/Kernel.lean` |
| Weighted two-form suffix, completed square | `disc_coords` | `Two/Suffix.lean` |
| Weighted two-form suffix, free-`q₀` integration | `lintegral_F_coords_le` (five-term bound `G`) | `Two/Suffix.lean` |
| Weighted two-form suffix, `J` bounds assembled | `lintegral_G_le` (`N₂ ≤ C · N2b`) | `Two/Kernel.lean` |
| Weighted two-form suffix, "locally integrable" | `setLIntegral_N2b_le`, `setLIntegral_box_F_le` (uniform on unit `Q`-discs) | `Two/Kernel.lean`, `Two/Suffix.lean` |
| One-form prefix decay | replaced by `lintegral_pre_lt_top` (see departure 5) | `Two/Prefix.lean` |
| Local averaging of a planar bound | not needed (see departure 6) | — |
| Proof of Theorem "Position two", weight | `norm_rpow_le_weight` | `Two/Assembly.lean` |
| Proof of Theorem "Position two", generators | `sublevel_indicator_le` | `Two/Assembly.lean` |
| Proof of Theorem "Position two", interface + Tonelli | `lintegral_W2_le`, `lintegral_W2_box_le`, `sublevel_two_le` | `Two/Assembly.lean` |
| Theorem "Position two" | `sublevelTwo` | `Two.lean` |

Coordinates: `lintegral_coords` writes `∫ dP` as `∫ dQ ∫ dv ∫ du ∫ dz` for `P = (z, Q, u, v)`,
through the measure-preserving `coordsEquiv`. This is proved like
`Downstream.measurePreserving_cubicEquiv_symm`.

## Departures from the note

1. **`eq:quadw` is proved by a split, not by a reference integral.** The parameter is
   `δ = d²` itself: `q = A((z - c)² - δ)`, so no complex square root is chosen.
   * On `|z - c| ≤ 2|δ|^{1/2}`, bound `|z|^γ ≤ |c|^γ + 2^γ|δ|^{γ/2}` and apply `eq:quad0`.
   * Outside, `|(z - c)² - δ| ≥ (3/4)|z - c|²`, and the tail power bound applies after
     translating by `c`.

   The proof uses `γ ≤ 1` (for `(x + y)^γ ≤ x^γ + y^γ`). Only `γ = 1/4` is needed. The constant
   is the explicit `quadW K t γ`. The note's reference integral
   `∫(1 + |z|^γ)|z² - 1|^{-t} < ∞` and the affine substitution are not formalized, because they
   are not used.
2. **One bound for `L_t`.** The note uses a separate argument for each `t`: the full plane at
   `t = 9/8`, Hölder at `8/7` for `t = 1`, and Cauchy–Schwarz for `t = 3/4`. `L_le` replaces
   these with the pointwise inequality `x^t ≤ x^{9/8} + 1` (for `0 ≤ t ≤ 9/8`) and
   `FullPlaneQuadratic (9/8)`. This gives `L_t(z) ≤ (2K + 4π)|z|^{-s}` for every `z` and every
   `1/8 ≤ s ≤ t`. For `t = 3/4` this is weaker than the note's uniform bound (`κ = 1/8` instead
   of `0`), but `a + κ = 15/8 < 2` still holds.
3. **Five terms instead of four.** The weighted factor is bounded by
   `|c|^{1/4} ≤ |v|^{-1/2}(1 + 3|h|^{1/4})` and `|δ|^{1/8} ≤ 4|h|^{3/8}|v|^{-1/2}`. The note
   absorbs `|h|^{1/4}` into `1 + |h|^{3/8}`. Here it stays as a separate term
   `|v|^{-7/4}|h|^{-7/8}` (`G`, `weighted_term_le`).
4. **No large-`|Q|` analysis of `J`.** Each `J_{a,t}(Q)` is bounded by `C|Q|^{-s}` for one
   exponent `s` with `a + s < 2`. That exponent is `s = 1/8`, except for `J_{5/4,9/8}`, which
   carries the factor `(1 + |Q|)^{1/4}` and takes `s = 1/2`. The result,
   `N₂(Q) ≤ C(|Q|^{-1/8} + |Q|^{-1/4} + |Q|^{-1/2})`, is **weaker than the note's `eq:n2`** at
   both ends: `|Q|^{-1/2}` near `0`, and only `|Q|^{-1/8}` at infinity. `eq:n2` itself is not
   formalized. The only consequence used is that `∫_{|Q - Q₀|<1} N₂` is bounded uniformly in
   `Q₀`. The change of variables `z = Qv` is not needed.
5. **The prefix: finiteness instead of decay.** The note's Lemma "One-form prefix decay"
   (`P₂(c) ≤ C(1 + |c|)^{-9/4}`, with the cube-slab substitution `eq:cubeslab`) is **not
   formalized**. Instead, `lintegral_pre_lt_top` proves that the weighted prefix volume is
   finite: `∫∫ V 𝟙_{preSet} < ∞`, where `preSet` keeps only `|b_k³|, |a_k b_k²| < 1` and
   `|a₁² b₁ - a₂² b₂| < 1`. This is the note's transverse-area bound without the slab, with
   `φ = max(1, ·)`:
   * On `|a₁| ≤ |a₂|`, the area in `b₂` is at most `π φ(|a₂|)^{-4}` and the area in `b₁` is at
     most `π φ(|a₁|)^{-1}`. With `V ≤ 3φ(|a₂|)^{1/4}`, the integrand is at most
     `3π² φ(|a₁|)^{-19/8} φ(|a₂|)^{-19/8}`, which is integrable on `ℂ²`.
   * The other half follows by symmetry.

   Equivalently, `∫ P₂(c) dc = π ∫∫ V' 𝟙_{preSet}`, where `V' = 1 + ‖(l₁, l₂)‖^{1/4} ≤ V` is the
   note's weight. So `P₂` is integrable, and its decay is not needed.
6. **Assembly without local averaging.** Tonelli runs in the order `g₂`, `g₁`, then `(l₁, l₂)`.
   * The `g₂`-integral is the `W₂`-weighted suffix mass of the unit box centred at `q¹₁`.
   * The `g₁`-integral is that of the unit box centred at `-(p¹₀ - p²₀)`.

   Both are at most `C · Msuf` uniformly (`lintegral_W2_box_le`). What remains is the prefix
   integral. The generator `p¹₀ - p²₀ + q¹₁` is used only to put `q¹₁` in a unit disc. The note's
   reduction to `∬_{|Q₁-Q₂|<1} N₂ N₂ P₂(-Q₁)` and its Lemma "Local averaging of a planar bound"
   are not formalized.
7. **The weight.** The prefix weight is `V = 1 + ‖l₁‖^{1/4} + ‖l₂‖^{1/4}`; the note uses
   `1 + ‖(l₁, l₂)‖^{1/4}`. The domination `‖w‖^{1/4} ≤ V W₂(g₁) W₂(g₂)` is
   `norm_rpow_le_weight`.
8. **No null-set arguments.** Inverse powers are `‖x‖ₑ⁻¹ ^ t` in `ℝ≥0∞`, which equals `∞` at
   `0`. On the degenerate fibres `v = 0` and `h = u² - Qv = 0`, the bound `G` is `∞`, so the
   pointwise inequality `∫ F dz ≤ C · G` holds everywhere.
9. **Upper-bound Tonelli.** The iterated-integral steps use `lintegral_prod_le`, which needs no
   measurability. Measurability is proved only where an equality is used: the swap of `g₁` and
   `l₂`, and the constant pull-outs.

## Errors or gaps found in the note

No statement used here is false, and every step that was formalized went through as written,
up to the reorganisations above. These steps were not formalized, so Lean does not check them:
* the reference integral in "Planar powers and quadratics";
* the `|Q| ≥ 1` rows of "An explicit two-variable integral";
* the exact exponents in `eq:n2`;
* "One-form prefix decay" with `eq:cubeslab`;
* "Local averaging of a planar bound";
* the position-two case of Section 7 (the shell corollary).

The following were checked by hand, and no error was found:
* the `E(L)` computation in "One-form prefix decay", and the `9|a|⁴`, three-to-one Jacobian of
  `eq:cubeslab`;
* the `|Q| ≥ 1` powers `-2/3, -1/2, -1/4, -1/4` in "Weighted two-form suffix";
* the completed square and the discriminant `16h³` (these two are also in Lean).

One remark on the note's Section 8: "The generator … supplies `P₂(−Q)` and its decay; it is
essential to this proof." The generator `p¹₀ - p²₀ + q¹₁` is essential, because without it `q¹₁`
is unconstrained and the integral diverges. Its *decay* is not essential: the prefix is
integrable without it (departure 5). This does not affect the theorem.

## Open

Nothing is open for `sublevelTwo` beyond the two interface hypotheses. These are not
formalized:
* the note's sharper intermediate statements: `eq:n2` as stated, "One-form prefix decay" and
  "Local averaging of a planar bound";
* the shell corollary at position two.
