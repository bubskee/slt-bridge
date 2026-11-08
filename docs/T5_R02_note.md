# T5 note: Lemma R0.2 (mixed identity group) is monomial-comparable after a shear (brief 04)

**Source.** resnet-bridge `readwrite/R0_scalar.md` at `c55350b`, Lemma R0.2 (read only):
`K = S² + Q²`, with `S = Σ wᵢ³ + Σ yⱼ` and `Q = Σ wᵢ⁶ + Σ yⱼ²`, where `w ∈ ℝ^p`, `y ∈ ℝ^q` and `q ≥ 1`. The claimed pair is
`J(p, q) = (1/2 + p/12 + (q−1)/4, 1)`.

The brief asked me to decide whether R0.2 is Newton-degenerate, and to write an obstruction note if it is not
monomial-comparable. **Verdict: it is not an obstruction.**

## 1. In the original coordinates it is not comparable to any monomial sum

Take `p = q = 1` and compare the points `(w, y) = (w, −w³)` and `(w, w³)`:
- at the first, `S = 0` and `K = 4w¹²`;
- at the second, `S = 2w³` and `K ≍ 4w⁶`.

A monomial sum `Σ |w|^α |y|^β` takes the same value at both points, because it only sees `|y|`. So `K / monoSum`
cannot stay bounded above and below as `w → 0`. In these coordinates the cancellation in `S` is real, and the
`Γ`-form of N2 does not apply.

## 2. After the triangular shear `y₁ ↦ S` it is comparable

R0.2's own proof makes this change of coordinates. In the coordinates `(w, S, y_{≥2})`, with
`P = Σ wᵢ⁶ + Σ_{j≥2} yⱼ²`, it shows `K ≍ S² + P²`. Since `P² ≍ Σ wᵢ¹² + Σ_{j≥2} yⱼ⁴` (all terms are nonnegative),

  `K ≍ S² + Σᵢ wᵢ¹² + Σ_{j≥2} yⱼ⁴`.

That is a pure-power monomial sum. Its Newton data is `t* = (1/2 + p/12 + (q−1)/4)⁻¹` with a single optimal
weight, so `m = 1`. This is the shape of `SLT.Zoo.MLP.pair_of_powΓ`, and it reproduces `J(p, q)` exactly. **So the
paper's pair agrees with N2. Nothing here needs Phong–Sturm** (compare `docs/T3_obstruction.md` §1, where the
cancellation is not removable by a change of coordinates).

The MLP hunt (`hunt_cancellation.md`) saw the same mechanism. A near-cancellation that is *linear in one
coordinate* (here `S` is linear in `y₁`) is absorbed into a coordinate change. What remains is monomial.

## 3. A wording point for the source (no effect on the result)

R0.2 calls the map `(w, y₁, y_{≥2}) ↦ (w, S, y_{≥2})` "linear with determinant one". It is **not linear**, since
`S` contains `Σ wᵢ³`. It is a triangular polynomial map `y₁ ↦ y₁ + Σwᵢ³ + Σ_{j≥2} yⱼ` with unit Jacobian, so it
still preserves Lebesgue measure. The box-sandwich claim also still holds: for `ρ ≤ 1`, the image of the box
of half-width `ρ` contains the box of half-width `ρ/(p + q)` and lies inside the box of half-width
`(p + q)ρ`. (`|S| ≤ qρ + pρ³`, and conversely `|y₁| ≤ |S| + Σ|wᵢ|³ + Σ_{j≥2}|yⱼ|`.) So the argument is fine as
written, apart from the word "linear".

## 4. Not built, and what it would take

I did not Lean-certify R0.2, because the brief's instruction for this item was a short look. A certificate for
`J(1, 1) = 7/12` would need three pieces:
- the shear, `MeasurePreserving` on `Fin 2 → ℝ` by Fubini plus translation invariance in `y`;
- a two-box sandwich lemma (`Z` on a box ≤ `Z` on the image ≤ `Z` on a larger box, all with the same pair);
- the comparison `S² + Q² ≍ S² + w¹²` on the shear box, which is elementary.

That is roughly 150 lines. General `(p, q)` adds index bookkeeping (`Fin.append`).

The approval covers T5 only. This is a candidate follow-up for Bobby to approve or not, not something I am
doing now.
