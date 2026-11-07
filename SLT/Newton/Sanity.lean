/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Newton.Statement

/-!
# Sanity checks for the multiplicity convention `m = dim O + 1`

`newtonMult Γ` is **defined** as `dim (affineSpan O) + 1`, where `O = optWeights Γ` is the set of
optimal simplex weights. The equivalence with `d - dim F` (with `F` the smallest face of the Newton
polyhedron containing `t*·𝟙`) is LP duality, which is not formalised. These lemmas pin the
convention
down on the brief's table by computing `O` explicitly:

| `Γ` | `t*` | `O` | `m` |
|---|---|---|---|
| `{2k}`, `d = 1` | `2k` | `{1}` | `1` |
| `{(2,2)}` | `2` | `segment (1,0) (0,1)` | `2` |
| `{(2,0),(0,2)}` | `1` | `{(1/2,1/2)}` | `1` |
| `{(2,0)}`, `d = 2` | `2` | `{(1,0)}` | `1` |
-/

@[expose] public section

namespace SLT.Newton

open Set Module

private theorem newtonMult_of_optWeights_singleton {d : ℕ} {Γ : Finset (Fin d → ℝ)} {p : Fin d → ℝ}
    (h : optWeights Γ = {p}) : newtonMult Γ = 1 := by
  rw [newtonMult, h, direction_affineSpan, vectorSpan_singleton, finrank_bot]

/-- `{2k}`, `d = 1`: `O = {1}`. -/
theorem optWeights_single (k : ℝ) :
    optWeights ({fun _ => 2 * k} : Finset (Fin 1 → ℝ)) = {fun _ => 1} := by
  ext u
  simp only [optWeights, newtonDist_single, IsNewtonCert, Finset.mem_singleton, forall_eq,
    Fin.sum_univ_one, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨-, h1, -⟩
    funext i; fin_cases i; exact h1
  · rintro rfl
    exact ⟨fun _ => zero_le_one, rfl, by simp⟩

/-- `{2k}`, `d = 1`: `m = 1` (N2 sanity). -/
theorem newtonMult_single (k : ℝ) : newtonMult ({fun _ => 2 * k} : Finset (Fin 1 → ℝ)) = 1 :=
  newtonMult_of_optWeights_singleton (optWeights_single k)

/-- `x² y²`: `O` is the whole simplex, the segment from `(1,0)` to `(0,1)`. -/
theorem optWeights_xy :
    optWeights ({![2, 2]} : Finset (Fin 2 → ℝ)) = segment ℝ ![1, 0] ![0, 1] := by
  ext u
  simp only [optWeights, newtonDist_xy, IsNewtonCert, Finset.mem_singleton, forall_eq,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mem_ofPred_eq]
  constructor
  · rintro ⟨h0, h1, -⟩
    refine ⟨u 0, u 1, h0 0, h0 1, h1, ?_⟩
    funext i; fin_cases i <;> simp
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨fun i => ?_, by simpa using hab, by simp; nlinarith⟩
    fin_cases i <;> simpa

/-- `x² y²`: `m = 2` (N2 sanity). -/
theorem newtonMult_xy : newtonMult ({![2, 2]} : Finset (Fin 2 → ℝ)) = 2 := by
  rw [newtonMult, optWeights_xy, ← convexHull_pair, affineSpan_convexHull, direction_affineSpan,
    vectorSpan_pair, finrank_span_singleton]
  intro h
  have := congrFun h 0
  simp at this

/-- `x² + y²`: `O = {(1/2, 1/2)}`. -/
theorem optWeights_sq_add_sq :
    optWeights ({![2, 0], ![0, 2]} : Finset (Fin 2 → ℝ)) = {![1 / 2, 1 / 2]} := by
  ext u
  simp only [optWeights, newtonDist_sq_add_sq, IsNewtonCert, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨-, h1, h2⟩
    have a := h2 ![2, 0] (by simp)
    have b := h2 ![0, 2] (by simp)
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 a b
    funext i; fin_cases i <;> simp <;> linarith
  · rintro rfl
    refine ⟨fun i => by fin_cases i <;> norm_num, by simp [Fin.sum_univ_two]; norm_num, ?_⟩
    intro α hα
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> simp [Fin.sum_univ_two]

/-- `x² + y²`: `m = 1` (N2 sanity). -/
theorem newtonMult_sq_add_sq : newtonMult ({![2, 0], ![0, 2]} : Finset (Fin 2 → ℝ)) = 1 :=
  newtonMult_of_optWeights_singleton optWeights_sq_add_sq

/-- `x²` in `d = 2`: `O = {(1, 0)}` (the face of `Γ₊` through `t*·𝟙` is non-compact). -/
theorem optWeights_sq_d2 : optWeights ({![2, 0]} : Finset (Fin 2 → ℝ)) = {![1, 0]} := by
  ext u
  simp only [optWeights, newtonDist_sq_d2, IsNewtonCert, Finset.mem_singleton, forall_eq,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨h0, h1, h2⟩
    have := h0 1
    funext i; fin_cases i <;> simp <;> nlinarith
  · rintro rfl
    exact ⟨fun i => by fin_cases i <;> norm_num, by simp, by simp⟩

/-- `x²` in `d = 2`: `m = 1` (N2 sanity). -/
theorem newtonMult_sq_d2 : newtonMult ({![2, 0]} : Finset (Fin 2 → ℝ)) = 1 :=
  newtonMult_of_optWeights_singleton optWeights_sq_d2

end SLT.Newton
