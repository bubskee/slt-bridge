/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Newton.Lower
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# N2, the statement (brief 01, stage N2)

This file defines the multiplicity and states the two-sided Newton theorem as a `Prop`
(`NewtonTwoSided d`), as approved in Bobby's statement review. **The proof is
`SLT.Newton.newtonTwoSided`** (`SLT/Newton/TwoSided.lean`). The symmetric-box corollary with a
prior density is `SLT.Newton.newton_box_units` (`SLT/Newton/Box.lean`).

**Convention.** The multiplicity is *defined* as `m = dim O + 1` (`newtonMult`). The sanity lemmas
in `SLT/Newton/Sanity.lean` pin it down on the brief's table.

**Multiplicity, certificate form.** Let `O = optWeights Γ` be the set of optimal simplex weights,
`O = { u ∈ Δ | t* ≤ ⟨α, u⟩ for all α ∈ Γ }`. Then `(1/t*)·O` is the minimising face of
`P = { u ≥ 0 | ⟨α, u⟩ ≥ 1 for all α }` for `⟨𝟙, u⟩`. That face is dual to the smallest face `F` of
`Γ₊` containing `t*·𝟙`, so `dim O = d - 1 - dim F`, and the brief's multiplicity is
`m = d - dim F = dim O + 1`. We take `newtonMult Γ = dim (affineSpan O) + 1` as the definition.
The duality step is **not** formalised; it is the "visibly equivalent" certificate form that the
brief allows.

Brief's table, `(t*, O, m)`:
* `{2k}`, `d = 1`: `t* = 2k`, `O = {1}`, `m = 1`.
* `{(2,2)}`: `t* = 2`, `O = Δ` (a segment), `m = 2`.
* `{(2,0),(0,2)}`: `t* = 1`, `O = {(1/2,1/2)}`, `m = 1`.
* `{(2,0)}`, `d = 2`: `t* = 2`, `O = {(1,0)}`, `m = 1` (the non-compact face).
-/

@[expose] public section

namespace SLT.Newton

open MeasureTheory Set

variable {d : ℕ}

/-- The optimal simplex weights `O = { u ∈ Δ | t* ≤ ⟨α,u⟩ ∀ α ∈ Γ }`. -/
def optWeights (Γ : Finset (Fin d → ℝ)) : Set (Fin d → ℝ) := {u | IsNewtonCert Γ (newtonDist Γ) u}

/-- The Newton multiplicity, **defined** as `m = dim O + 1`, where `O = optWeights Γ`. It equals
`d - dim F` by LP duality, which is not formalised; see `SLT/Newton/Sanity.lean`. -/
noncomputable def newtonMult (Γ : Finset (Fin d → ℝ)) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (optWeights Γ)).direction + 1

/-- **N2** (proved as `newtonTwoSided`): if `K` is comparable to `∑_{α∈Γ} |w|^α` on `[0,1]^d` (positive
constants in both directions) and `t* > 0`, then `Z` has learning pair `(1/t*, m)`. -/
def NewtonTwoSided (d : ℕ) : Prop :=
  ∀ (Γ : Finset (Fin d → ℝ)), (∀ α ∈ Γ, ∀ i, 0 ≤ α i) → 0 < newtonDist Γ →
    ∀ (K : (Fin d → ℝ) → ℝ), Measurable K → ∀ c C : ℝ, 0 < c →
      (∀ w ∈ Icc (0 : Fin d → ℝ) 1,
        c * ∑ α ∈ Γ, monomial α w ≤ K w ∧ K w ≤ C * ∑ α ∈ Γ, monomial α w) →
      HasLaplacePair (Z (volume.restrict (Icc (0 : Fin d → ℝ) 1)) K) (newtonDist Γ)⁻¹
        (newtonMult Γ)

end SLT.Newton
