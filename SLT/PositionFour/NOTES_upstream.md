# Upstream half (note §1): working notes

Branch `c4-upstream`. Source: `forum/complex_position_four/complex_position_four.tex`, §1
("Row pushforwards, including weighted fibers").

## Status

Both interface statements of `Defs.lean` are **proved** for every `0 ≤ β < 2`. No named hypothesis
remains open. In particular step 3 (the two-cube pushforward) is proved (`twoCubeBound`), not
assumed.

```lean
theorem upstream_densityBound (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 2) : ∃ C, DensityBound β C
theorem upstream_locallyFiniteRow (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 2) : LocallyFiniteRow β
```

The explicit constant is `densityConst β = 3 · (2/9) · (4^β · (refFibre β).toReal + 1)`
(`densityBound_holds`).

* Build: `lake build SLT.PositionFour.Upstream`. Zero warnings in our files after a clean rebuild.
* Audit: `lake env lean SLT/PositionFour/AuditUpstream.lean`. 169/169 public declarations, all on
  `[propext, Classical.choice, Quot.sound]`. The list was generated with `scripts/DumpDecls.lean`
  (prefix `SLT.PositionFour.Upstream`). It includes one auto-generated
  `ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero.congr_simp`, created by a `simp` in
  `Area.lean`.
* Batteries `#lint` (all default linters plus `docBlameThm`) over `SLT`, with the upstream modules
  imported: no errors.
* No `sorry`, `admit` or `native_decide`.

## Modules (import order)

| Module | Content |
|---|---|
| `Algebra` | `det2`, `twoCube`, `refCubic`, substitution actions `formAct`/`quadAct`/`cubicAct`; the identities of `verify_algebra.py` by `ring` |
| `Sylvester` | existence `exists_twoCube_eq`; uniqueness `twoCube_eq_twoCube`; fibre `≤ 18`; norm dichotomy `norm_twoCube_cases` |
| `Area` | change of variables with bounded multiplicity, plus the covering inequality (general `f : E → E`) |
| `Coords` | real determinant `= |det_ℂ|²`; linear substitutions; measure-preserving coordinates; `{det = 0}` is null |
| `Planar` | `∫_{|z|<r} |z|^{-p} < ∞` (`p < 2`), `∫ (1+|z|)^{-q} < ∞` (`q > 2`), two-point singularities |
| `Reference` | step 1: `∬ w_β(x) w_β(y) |x-y|^{-2/3} < ∞` |
| `RefFibre` | cube substitution (degree 3), root substitution (degree 2), `refFibre_lt_top` (`ρ_β(P*) < ∞`) |
| `TwoCube` | step 3: Jacobian `9 det⁴`, `twoCubeBound : TwoCubeBound (2/9)` |
| `Density` | step 4: Tonelli against the third form, transport, equation (2), `densityBound_holds` |
| `Cusp` | full-plane quadratic integral at exponent `4/3`, shifted-disc bound |
| `Local` | step 5: cone chart, four `GL₂` charts, `|𝔇|^{-4/3} ∈ L¹_loc`, `locallyFiniteRow` |

## Departures from the note (all deliberate, none weakens a statement)

1. **Step 1, Young.** Young's inequality is replaced by the pointwise inequality
   `A B k ≤ (AB)^{4/3} + (A^{4/3} + B^{4/3}) k²` (`mul_mul_le_amgm`). After Tonelli and translation
   invariance this needs exactly the note's inputs: `w_β ∈ L¹`, `w_β ∈ L^{4/3}`, `K ∈ L²`.
2. **Step 3 is an upper bound only.** We prove `Ψ_* Leb ≤ (2/9) |𝔇|^{-4/3} Leb` in moment
   coordinates. This agrees with the note's `(2/9)|Disc|^{-4/3}` in ordinary coordinates once the
   factors `81` (Lebesgue) and `27^{4/3} = 81` (discriminant) are tracked. The proof uses Sylvester's
   uniqueness to bound the fibre by 18 and a general multiplicity inequality (`Area.lean`) built from
   Mathlib's partition into almost-linear pieces. Equality is not proved; it is not needed.
3. **Step 4 avoids densities and measure equivariance.** Instead of `ρ_β` and the `GL₂`-equivariance
   of `rowMeasure`, we prove the measure inequality `rowMeasure β ≤ (2/3) ρ̃_β · Leb`, where
   `ρ̃_β(P) = ∫ ‖l‖^β |𝔇(P - l³)|^{-4/3} dl` (`lintegral_rowMeasure_le`). The transport
   `ρ̃_β(g P*) ≤ |𝔇|^{-1} (2‖g‖)^β ρ̃_β(P*)` is then a linear substitution `l = g u` in `ℂ²` with
   Jacobian `|det g|²` (`rhoTilde_le_of_twoCube`). The note's source and target Jacobians
   `|det g|⁶, |det g|¹²` are not used. The exact homogeneity `ρ_β(rP) = r^{-4+β/3} ρ_β(P)` is not
   proved; nothing upstream needs it.
4. **Norm bound with explicit constants.** `norm_twoCube_cases`: either `‖g‖³ ≤ 2‖P‖` or
   `‖g‖² |det g|² ≤ 4 ‖H(P)‖`, for sup norms. Together with `‖l m‖ ≥ ‖l‖ ‖m‖ / 2` and
   `‖l³‖ = ‖l‖³` this gives `(2‖g‖)^β ≤ 4^β (‖P‖^{β/3} + ‖H‖^{β/2} |𝔇|^{-β/6})`.
5. **Weight at `P*`.** We use `‖u‖^β = max(|U|, |V|)^{β/3} ≤ (1+|x|)^{β/3} (1+|y|)^{β/3}`, the
   sup-norm form of the note's `(|u|²+|v|²)^{β/2}` bound. The exponent `β/3` matters: the cruder
   `(1+|U|)(1+|V|)` would give `2β/3` and need `β < 1`.
6. **The set `{𝔇 = 0}`.** We never prove it is Lebesgue-null. Off `P = 0`, `densityBound β = ∞` there
   (its first summand is `ofReal(‖P‖^{β/3}) · ∞`), so the bound holds there trivially. The `+ 1` in
   `densityConst` makes the constant positive for this. The point `P = 0` is null.
   **Caution for downstream:** `densityBound β 0 = 0` for `β > 0` (`0^{β/3} · ∞ = 0` in `ℝ≥0∞`),
   while it is `∞` for `β = 0`. This is harmless on a null point, but it is not "∞ wherever
   `𝔇 = 0`", contrary to the docstring of `densityBound` in `Defs.lean` taken literally.
7. **Local finiteness, different chart.** The note uses the cusp chart `𝔇 = 4q³ + r²` at `P₀ = 1`,
   homogeneity at `0`, and "smooth points are easier". We instead prove the stronger statement
   that `|𝔇|^{-4/3}` is integrable on balls (`lintegral_closedBall_twoCubeDensity_lt_top`), and
   dominate `densityBound β` by it on balls. This step uses `1 + β/6 ≤ 4/3`, i.e. `β ≤ 2`. The proof
   has three parts:
   * one cone chart `{‖P‖ ≤ C|P₀|}` through the origin, where the full-plane `P₃`-integral of the
     quadratic `𝔇` gives `|P₀|^{-4/3} |P₁² - P₀P₂|^{-1}` (discriminant `16(P₁² - P₀P₂)³`, as in
     `verify_algebra.py`);
   * a shifted-disc bound in `P₂`, followed by `P₁`, which leaves `|P₀|^{2/3}`;
   * four unimodular substitutions (identity, `s ↔ t`, `t ↦ s ± t`), which cover cubic space
     because `‖P‖ ≤ max(|P(1,0)|, |P(0,1)|, |P(1,1)|, |P(1,-1)|)`, and which preserve `𝔇` and
     Lebesgue measure (`det_ℂ = det(g)⁶`, `det_cubicActL`).

   A side consequence: the two-cube pushforward `Ψ_* Leb` is itself locally finite.

## No error found in §1

Every step of §1 that the interface needs went through as written, up to the reorganisations
above. The constants agree with the note: two-cube density `2/9`, Jacobian `81 det⁴` (ordinary
coordinates) = `9 det⁴` (moment coordinates), and 18 preimages.

Not formalised, because the interface does not need them: positivity of any constant, the exact
formula `ρ₀ = c |𝔇|^{-1}`, lower bounds, homogeneity of `ρ_β`, and nullity of `{𝔇 = 0}`.
