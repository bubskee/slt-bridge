/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Three.Suffix
public import SLT.MiddlePositions.Three.Marginal
public import SLT.MiddlePositions.Three.Prefix
public import SLT.MiddlePositions.Three.Assembly

/-!
# The complex margin at position three

Theorem "Position three" of `complex_middle_positions.tex` (2026-11-09), from the interface of
`SLT.MiddlePositions.Defs`:
`∫_{‖R₃ w‖ < 1} ‖w‖^{1/4} dw < ∞` over `Row3 × Row3 ≃ ℂ¹²` (sup norms), assuming
`WeightedTwoCubeBound C`, `LocallyIntegrableF` and `FullPlaneQuadratic t K` for `1 < t < 2`. Only
`t = 4/3` and `t = 11/8` are used.

Module map:

* `Three.Suffix`: the weighted one-form suffix kernel `N₃` (the note's Lemma "Weighted one-form
  suffix"), its pushforward identity and the bounds `N₃ ≲ |Q|^{-1}`, `N₃ ≲ |Q|^{-7/6}`;
* `Three.Marginal`: the two-cube transverse marginal `m(U, V)` (Lemma "Pointwise bounds on
  explicit regions"): outer and central bounds, the near part in `L¹`, the far part in `L²`;
* `Three.Prefix`: the abstract translated `L¹ + L²` kernel bound and the uniform prefix bound
  (Lemma "Uniform translated prefix bound");
* `Three.Assembly`: the product weight, the eleven constraints, Tonelli, the suffix double
  integral and the theorem.

Notes, with the note-versus-Lean correspondence and every departure:
`SLT/MiddlePositions/NOTES_three.md`. Axiom audit: the root `Audit.lean`.
-/

@[expose] public section

namespace SLT.MiddlePositions.Three

/-- **Theorem (position three)**: `∫_{‖R₃ w‖ < 1} ‖w‖^{1/4} dw < ∞`, from the interface
`WeightedTwoCubeBound C`, `LocallyIntegrableF` and `FullPlaneQuadratic` for `1 < t < 2`. -/
theorem sublevelThree {C : ℝ} (hW : WeightedTwoCubeBound C) (hF : LocallyIntegrableF)
    (hQ : ∀ t : ℝ, 1 < t → t < 2 → ∃ K, FullPlaneQuadratic t K) : SublevelThree :=
  sublevelThree_of_interface hW hF hQ

end SLT.MiddlePositions.Three
