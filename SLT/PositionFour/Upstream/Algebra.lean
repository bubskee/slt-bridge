/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Defs

/-!
# Algebra of binary cubics (note §1, the identities of `verify_algebra.py`)

The two-cube map `Ψ(l, m) = l³ + m³`, the substitution actions of a pair of forms `g = (l, m)` on
forms, quadratics and cubics, and the polynomial identities the note uses:

* `disc_twoCube`: `𝔇(l³ + m³) = det(l, m)⁶`;
* `hess_twoCube`: `H(l³ + m³) = det(l, m)² · l m` (Hessian covariance at `P* = s³ + t³`);
* `disc_cubicAct`, `hess_cubicAct`: covariance of `𝔇` and `H` under substitution;
* `disc_eq_hess`: `𝔇 = disc H`, the discriminant of the Hessian quadratic;
* `disc_refCubic_sub_cube`: `𝔇(P* - u³) = (1 - u₁³ - u₂³)² - 4 u₁³ u₂³`;
* `root_substitution`: `(1 - U - V)² - 4 U V = (x - y)²` for `U = x y`, `V = (1 - x)(1 - y)`.

A pair `g = (l, m)` with `l = a s + b t`, `m = c s + d t` acts by substitution `(s, t) ↦ (l, m)`.
On forms this is `u ↦ u₁ l + u₂ m`; on cubics it is `P(s, t) ↦ P(l, m)`, so `g · P* = l³ + m³`.
-/

@[expose] public section

namespace SLT.PositionFour

/-- The determinant `a d - b c` of a pair of forms `(a s + b t, c s + d t)`. -/
def det2 (g : Form × Form) : ℂ := g.1.1 * g.2.2 - g.1.2 * g.2.1

/-- The two-cube map `Ψ(l, m) = l³ + m³`. -/
def twoCube (g : Form × Form) : Cubic := cube g.1 + cube g.2

/-- The reference cubic `P* = s³ + t³`. -/
def refCubic : Cubic := ![1, 0, 0, 1]

/-- The product `l m` of two forms, as the coefficients of `s²`, `s t`, `t²`. -/
def formMul (l m : Form) : Fin 3 → ℂ := ![l.1 * m.1, l.1 * m.2 + l.2 * m.1, l.2 * m.2]

/-- Substitution on forms: `u = u₁ s + u₂ t ↦ u₁ l + u₂ m`. -/
def formAct (g : Form × Form) (u : Form) : Form :=
  (u.1 * g.1.1 + u.2 * g.2.1, u.1 * g.1.2 + u.2 * g.2.2)

/-- Substitution on quadratics: `h₀ s² + h₁ s t + h₂ t² ↦ h₀ l² + h₁ l m + h₂ m²`. -/
def quadAct (g : Form × Form) (h : Fin 3 → ℂ) : Fin 3 → ℂ :=
  let a := g.1.1; let b := g.1.2; let c := g.2.1; let d := g.2.2
  ![h 0 * a ^ 2 + h 1 * a * c + h 2 * c ^ 2,
    2 * h 0 * a * b + h 1 * (a * d + b * c) + 2 * h 2 * c * d,
    h 0 * b ^ 2 + h 1 * b * d + h 2 * d ^ 2]

/-- Substitution on cubics in moment coordinates: `P(s, t) ↦ P(l, m)`. -/
def cubicAct (g : Form × Form) (P : Cubic) : Cubic :=
  let a := g.1.1; let b := g.1.2; let c := g.2.1; let d := g.2.2
  ![P 0 * a ^ 3 + 3 * P 1 * a ^ 2 * c + 3 * P 2 * a * c ^ 2 + P 3 * c ^ 3,
    P 0 * a ^ 2 * b + P 1 * (2 * a * b * c + a ^ 2 * d) + P 2 * (b * c ^ 2 + 2 * a * c * d)
      + P 3 * c ^ 2 * d,
    P 0 * a * b ^ 2 + P 1 * (b ^ 2 * c + 2 * a * b * d) + P 2 * (a * d ^ 2 + 2 * b * c * d)
      + P 3 * c * d ^ 2,
    P 0 * b ^ 3 + 3 * P 1 * b ^ 2 * d + 3 * P 2 * b * d ^ 2 + P 3 * d ^ 3]

/-- `𝔇(l³ + m³) = det(l, m)⁶`. -/
theorem disc_twoCube (g : Form × Form) : disc (twoCube g) = det2 g ^ 6 := by
  simp only [disc, twoCube, cube, det2, Pi.add_apply, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- Hessian covariance: `H(l³ + m³) = det(l, m)² · l m`. -/
theorem hess_twoCube (g : Form × Form) :
    hess (twoCube g) = det2 g ^ 2 • formMul g.1 g.2 := by
  ext i
  fin_cases i <;>
    simp [hess, twoCube, cube, det2, formMul] <;> ring

/-- `P* = s³ + t³` is carried to `l³ + m³`. -/
theorem cubicAct_refCubic (g : Form × Form) : cubicAct g refCubic = twoCube g := by
  ext i
  fin_cases i <;> simp [cubicAct, refCubic, twoCube, cube]

/-- Substitution commutes with cubing: `(u₁ l + u₂ m)³ = g · u³`. -/
theorem cube_formAct (g : Form × Form) (u : Form) :
    cube (formAct g u) = cubicAct g (cube u) := by
  ext i
  fin_cases i <;> simp [cubicAct, cube, formAct] <;> ring

/-- Substitution on cubics is additive. -/
theorem cubicAct_sub (g : Form × Form) (P Q : Cubic) :
    cubicAct g (P - Q) = cubicAct g P - cubicAct g Q := by
  ext i
  fin_cases i <;> simp [cubicAct] <;> ring

/-- `l³ + m³ - (u₁ l + u₂ m)³ = g · (P* - u³)`. -/
theorem twoCube_sub_cube_formAct (g : Form × Form) (u : Form) :
    twoCube g - cube (formAct g u) = cubicAct g (refCubic - cube u) := by
  rw [cubicAct_sub, cubicAct_refCubic, cube_formAct]

/-- Covariance of the discriminant: `𝔇(g · P) = det(g)⁶ 𝔇(P)`. -/
theorem disc_cubicAct (g : Form × Form) (P : Cubic) :
    disc (cubicAct g P) = det2 g ^ 6 * disc P := by
  simp only [disc, cubicAct, det2, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Covariance of the Hessian: `H(g · P) = det(g)² · g · H(P)`. -/
theorem hess_cubicAct (g : Form × Form) (P : Cubic) :
    hess (cubicAct g P) = det2 g ^ 2 • quadAct g (hess P) := by
  ext i
  fin_cases i <;> simp [hess, cubicAct, quadAct, det2] <;> ring

/-- `𝔇` is the discriminant of the Hessian quadratic: `𝔇 = H₁² - 4 H₀ H₂`. -/
theorem disc_eq_hess (P : Cubic) : disc P = hess P 1 ^ 2 - 4 * hess P 0 * hess P 2 := by
  simp only [disc, hess, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The reference discriminant: `𝔇(P* - u³) = (1 - u₁³ - u₂³)² - 4 u₁³ u₂³`. -/
theorem disc_refCubic_sub_cube (u : Form) :
    disc (refCubic - cube u) = (1 - u.1 ^ 3 - u.2 ^ 3) ^ 2 - 4 * u.1 ^ 3 * u.2 ^ 3 := by
  simp only [disc, refCubic, cube, Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- The root substitution: `(1 - U - V)² - 4 U V = (x - y)²` for `U = x y`,
`V = (1 - x)(1 - y)`. -/
theorem root_substitution (x y : ℂ) :
    (1 - x * y - (1 - x) * (1 - y)) ^ 2 - 4 * (x * y) * ((1 - x) * (1 - y)) = (x - y) ^ 2 := by
  ring

/-- The quadratic substitution carries `s t` to `l m`. -/
theorem quadAct_st (g : Form × Form) : quadAct g ![0, 1, 0] = formMul g.1 g.2 := by
  ext i
  fin_cases i <;> simp [quadAct, formMul]

/-- The discriminant of `𝔇` as a quadratic in `P₃` is `16 (P₁² - P₀P₂)³`. -/
theorem discr_disc (P₀ P₁ P₂ : ℂ) :
    (4 * P₁ ^ 3 - 6 * P₀ * P₁ * P₂) ^ 2 - 4 * P₀ ^ 2 * (4 * P₀ * P₂ ^ 3 - 3 * P₁ ^ 2 * P₂ ^ 2) =
      16 * (P₁ ^ 2 - P₀ * P₂) ^ 3 := by ring

end SLT.PositionFour
