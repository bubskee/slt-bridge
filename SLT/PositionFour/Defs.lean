/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Shared definitions for the complex position-four threshold

Source: the note `complex_position_four.tex` (2026-11-09), on the leading map of the width-two
shear at position four.

**This file is identical on the branches `c4-downstream` and `c4-upstream`,** so that the two merge
cleanly. Do not edit it on one branch only.

Norms are Mathlib's defaults: the sup norm on `ℂ × ℂ` and on `Fin n → ℂ`. Measures are `volume`.

The last section is the **density interface** between the two branches. `c4-upstream` proves
`DensityBound` and `LocallyFiniteRow` (the note's Section 1). `c4-downstream` assumes them and
proves the finiteness of the weighted sublevel volume (the note's Sections 2 and 3).
-/

@[expose] public section

namespace SLT.PositionFour

open MeasureTheory
open scoped ENNReal NNReal

/-- A binary linear form `a s + b t`, as its coefficient pair `(a, b)`. -/
abbrev Form := ℂ × ℂ

/-- A binary cubic in moment coordinates: `P = P₀ s³ + 3 P₁ s² t + 3 P₂ s t² + P₃ t³`. -/
abbrev Cubic := Fin 4 → ℂ

/-- The cube of a linear form in moment coordinates: `(a s + b t)³ ↦ (a³, a² b, a b², b³)`. -/
def cube (l : Form) : Cubic := ![l.1 ^ 3, l.1 ^ 2 * l.2, l.1 * l.2 ^ 2, l.2 ^ 3]

/-- A row of the three inactive blocks: three linear forms. -/
abbrev Row := Fin 3 → Form

/-- The row cubic `T(l₁, l₂, l₃) = l₁³ + l₂³ + l₃³`. -/
def rowCubic (r : Row) : Cubic := ∑ i, cube (r i)

/-- `𝔇(P) = -Disc(P) / 27`, a quartic in the moment coordinates. -/
def disc (P : Cubic) : ℂ :=
  P 0 ^ 2 * P 3 ^ 2 - 6 * P 0 * P 1 * P 2 * P 3 + 4 * P 0 * P 2 ^ 3 + 4 * P 1 ^ 3 * P 3
    - 3 * P 1 ^ 2 * P 2 ^ 2

/-- The Hessian covariant of `P`, as the coefficients of `s²`, `s t`, `t²`. -/
def hess (P : Cubic) : Fin 3 → ℂ :=
  ![P 0 * P 2 - P 1 ^ 2, P 0 * P 3 - P 1 * P 2, P 1 * P 3 - P 2 ^ 2]

/-- The position-four leading map on two rows, in row-cubic coordinates:
`R = (lam₁ - lam₂, y₁, y₂)`, where `lam = (P₀, P₁)` and `y = (P₂, P₃)` for each row cubic.
In the raw variables this is `(Φ(A) - Φ(C), A²B - C²D, AB², Φ(B), CD², Φ(D))`. -/
def leadingMap (w : Row × Row) : Fin 6 → ℂ :=
  ![rowCubic w.1 0 - rowCubic w.2 0, rowCubic w.1 1 - rowCubic w.2 1,
    rowCubic w.1 2, rowCubic w.1 3, rowCubic w.2 2, rowCubic w.2 3]

/-- The row weight `W_β(l) = ∑ᵢ ‖lᵢ‖ ^ β`. -/
noncomputable def rowWeight (β : ℝ) (r : Row) : ℝ := ∑ i, ‖r i‖ ^ β

/-! ### The density interface -/

/-- The pushforward to cubic space of `W_β` times Lebesgue measure on a row. At `β = 0` the weight
is the constant `3`, so `rowMeasure 0` is three times the plain pushforward of Lebesgue measure. -/
noncomputable def rowMeasure (β : ℝ) : Measure Cubic :=
  ((volume : Measure Row).withDensity fun r => ENNReal.ofReal (rowWeight β r)).map rowCubic

/-- The bounding density of the note's equation (2):
`‖P‖^(β/3) |𝔇(P)|⁻¹ + ‖H(P)‖^(β/2) |𝔇(P)|^(-1-β/6)`, with value `∞` where `𝔇(P) = 0`. -/
noncomputable def densityBound (β : ℝ) (P : Cubic) : ℝ≥0∞ :=
  ENNReal.ofReal (‖P‖ ^ (β / 3)) * (‖disc P‖₊ : ℝ≥0∞)⁻¹
    + ENNReal.ofReal (‖hess P‖ ^ (β / 2)) * ((‖disc P‖₊ : ℝ≥0∞)⁻¹) ^ (1 + β / 6)

/-- **Interface, part 1.** The weighted pushforward is dominated by `C` times the bounding
density. -/
def DensityBound (β C : ℝ) : Prop :=
  rowMeasure β ≤ ENNReal.ofReal C • (volume : Measure Cubic).withDensity (densityBound β)

/-- **Interface, part 2.** The weighted pushforward is finite on bounded sets. -/
def LocallyFiniteRow (β : ℝ) : Prop :=
  ∀ r : ℝ, rowMeasure β (Metric.closedBall 0 r) < ∞

end SLT.PositionFour
