# Complex position four: downstream half (working notes)

> Historical working note of the session that wrote this code. Since the consolidation, some
> files and declarations have moved to `SLT/Pushforward` or been merged, and the per-directory
> audit files are replaced by the root `Audit.lean`. Current locations and the list of removed
> or renamed declarations: `SLT/Pushforward/NOTES.md`.

Branch `c4-downstream`, worktree `slt-bridge-c4a`. This is Sections 2 and 3 of
`forum/complex_position_four/complex_position_four.tex` (2026-11-09), plus the shell form that
paper 2 consumes. It assumes the density interface of `SLT/PositionFour/Defs.lean` (unchanged).

Build: `lake build SLT.PositionFour.Downstream`, with zero warnings.
Audit: `lake env lean SLT/PositionFour/AuditDownstream.lean`. It has 92 lines, all on
`[propext, Classical.choice, Quot.sound]`. The Batteries linters, including `docBlameThm`, pass on
the downstream modules.

All declarations are in the namespace `SLT.PositionFour.Downstream`. This keeps them clear of
upstream names: upstream also defines a `cubicEquiv`.

## Results

| Note | Lean | Hypotheses |
|---|---|---|
| Lemma 1 | `lemma_one` | none: it is about `densityBound`, the explicit function |
| §3, weighted sublevel volume | `sublevel_weighted_lt_top` | `DensityBound 0 C₀`, `DensityBound β C`, `LocallyFiniteRow 0`, `LocallyFiniteRow β` |
| §3, endpoint (unit sublevel volume) | `volume_sublevel_lt_top` | `DensityBound 0 C₀`, `LocallyFiniteRow 0` |
| shell form, `s < 13/3` | `shell_lintegral_lt_top`, `integrableOn_shell`, `shell_lintegral_lt_top_of_interface` | the interface at `0` and at one `β` with `6s - 24 < β < 2`; or at every `β ∈ [0,2)` |

## The soft spot

Lemma 1 is **true as stated** (`‖λ‖ > 1`, sup norm on `λ = (P₀, P₁)`). The note derives (central)
and (outer) only for small `ε`, and never treats `P₀ → 0`. Both gaps are closed by proving the
pointwise bounds directly in `λ`, for every `‖λ‖ ≥ 1`, without spherical coordinates.

* **Every radius.** The two-root estimate (`Quadratic.lean`,
  `lintegral_ball_inv_quadratic_le`) holds on a disc of any radius:
  `∫_{|z|<R} |A z² + Bz + C|^{-1-α} ≤ c R^η |A|^{b-1-α} |B²-4AC|^{-b/2}` with `b = 2α + η`. The
  proof splits pointwise into the two single poles. Nothing assumes `ε` small.
* **Directions near `P₀ = 0`.** The one-dominant-root estimate
  (`lintegral_ball_one_inv_quadratic_le`) assumes `8|A| ≤ |B|` and allows `A = 0`. On the unit
  disc, `|q(z)| ≥ (|B|/4)|z - r|` for one root `r`. For `𝔇`, `A = P₀²` and `B = 4P₁³ - 6P₀P₁P₂`
  (the reader's "∂𝔇/∂P₃ is a unit"). On the outer region
  `{|P₁| ≥ 1, 6|P₀| ≤ |P₁|², 8|P₀|² ≤ |P₁|³}` this gives `|B| ≥ 3|P₁|³ ≥ 8|A|`, uniformly down to
  `P₀ = 0`, where `𝔇` is linear in `P₃`.
* **The rest of `‖λ‖ > 1`** (`central_facts`) has `|P₀| > 1/9`, `|P₁|³ ≤ 64|P₀|²` and
  `‖λ‖ ≤ 9|P₀|`. The central bound's negative powers of `|P₀|` are therefore harmless there, with
  no smallness needed.

The bounds come out as follows.

* **Central**: `m_β ≲ |P₀|^{-(2 - β/3 - η/2)}`. Integrated over
  `{|P₀| > 1/9, |P₁| ≤ 4|P₀|^{2/3}}`, it is finite iff `p(2 - β/3 - η/2) > 10/3`.
* **Outer**: `m_β ≲ |P₁|^{β/2 - 3}`. Integrated over `{|P₁| > 1/2, |P₀| ≤ |P₁|^{3/2}}`, it is
  finite iff `p(3 - β/2) > 5`, that is, iff `p > 10/(6-β)`.

The two regions meet at `|P₁| ≍ |P₀|^{2/3}`, the note's `|φ| ≍ ε^{1/3}`. Both give exactly the
note's threshold, so nothing is weakened.

## Departures from the note

1. **No spherical coordinates and no charts.** Lemma 1 is proved by pointwise bounds on `m_β(λ)`
   in the two regions above, then iterated planar integrals (`lintegral_slab_lt_top`).
2. **The logarithm is replaced by a power.** `1 + log(1/ε)` becomes `|P₀|^{η/2}`, with
   `η = min(1/2, 2 - β/3 - 10/(3p))`. This is legitimate because the condition `p > 10/(6-β)` is
   strict.
3. **The Hessian weight is split** as in the note: `‖H‖ ≤ |P₁² - P₀P₂| + (|P₀| + |P₁| + 1)` on the
   box, and `(x + N)^{3α} ≤ x^{3α} + N^{3α}`. The cruder bound `‖H‖ ≲ |P₁|² + |P₀|` would lose
   `|P₀|^α` and only reach `β < 4/3`.
4. **§3, compact part.** The note uses local integrability of the density. Here the compact part
   `‖λ₁‖ ≤ 2` lies in `closedBall 0 2 × closedBall 0 3`, which is finite directly by
   `LocallyFiniteRow`.
5. **§3, far part.** Hölder is applied on `ℂ² × ℂ²` to `𝟙{|λ₁-λ₂|<1} g₁(λ₁) g₂(λ₂)`; no Young
   inequality is used. The exponents are explicit: `p = 20/(10-β)` for the weighted row and
   `q = 20/(10+β)` for the unweighted one. The weight `W_β(w₁) + W_β(w₂)` is split, and `W₀ = 3`
   is used on the other row, giving the two symmetric product measures
   `rowMeasure β ⊗ rowMeasure 0` and `rowMeasure 0 ⊗ rowMeasure β`.
6. **Shell form.** The note's exact polar identity is replaced by a dyadic inequality
   (`Shell.lean`):
   * scaling by `2^k/2` maps `A_k = {w ∈ shell : 8^k‖R‖ ≤ 1}` into the unit sublevel set,
     where `‖w‖ ≥ 2^k/4`;
   * so `vol(A_k) ≲ I_β 2^{-k(24+β)}`, with `I_β = ∫_{‖R‖<1} ‖w‖^β ≤` the §3 integral;
   * a geometric series finishes the case `s > 0`;
   * `s ≤ 0` holds because `‖R‖ ≤ 6` on the unit ball.

   The shell is `{1/2 ≤ ‖w‖ < 1}` in the sup norm of `Row × Row` (the max of the 12 complex
   moduli), the library's convention. The Euclidean `S²³` statement of the theorem is not
   formalised; the two are equivalent by homogeneity, but that equivalence is not in Lean.
7. **Only the upper direction is formalised.** The obstruction at `p ≥ 26/3` (the note's §4,
   the aligned family) was not part of this task.

## Named hypotheses still open

Only the interface in `Defs.lean`: `DensityBound β C` and `LocallyFiniteRow β`, at `β = 0` and
at the `β` used. The upstream branch proves these; see `c4-upstream`. Nothing else is assumed.

## Module map

* `Downstream/Radial.lean`: polar coordinates for radial functions on `ℂ`; ball and tail integrals
  of `|z - c|^{-s}`.
* `Downstream/Quadratic.lean`: the two-root and one-dominant-root disc integrals; factorisation of
  quadratics.
* `Downstream/Marginal.lean`: `toCubic`, `transverseMarginal`, `𝔇` as a quadratic in `P₃`, and
  the central and outer pointwise bounds.
* `Downstream/LemmaOne.lean`: the region split and Lemma 1.
* `Downstream/Finiteness.lean`: `cubicEquiv` (measure preserving), the sublevel set in row-cubic
  coordinates, the Hölder near-diagonal bound, and §3.
* `Downstream/Shell.lean`: homogeneity, `‖R‖ ≤ 6`, the Haar instance and dimension 24 on
  `Row × Row`, and the shell theorems.
