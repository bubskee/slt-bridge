/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
import VectorSLT
import SLT

/-!
# Zoo: the complex leading maps are the network's

The core proves strict complex integrability margins for three maps on `ℂ¹²`:
`SLT.MiddlePositions.R2`, `SLT.MiddlePositions.R3` and `SLT.PositionFour.leadingMap`
(`SLT.Pushforward.strictShellMargin_leadingMaps`). Those maps are defined in the core by explicit
formulas, with no reference to a network.

`vector-slt-lean` (`VectorSLT/LeadingMap`) proves, for the depth-four cubic network with the shear
`A₀` at paper positions two, three and four, that the `ε³` coefficient of the error is an
injective linear image of four active coordinates and of real maps `VectorSLT.LeadingMap.R2`,
`R3`, `leadingMap`, which are written with the same formulas over `ℝ`.

This file closes the loop: on real inputs, the core's complex maps are the complexifications of
those real maps (`R2_complexify`, `R3_complexify`, `leadingMap_complexify`). Hence the leading
term of the network error vanishes exactly when the active coordinates and the core's complex
leading map both vanish (`lead_eq_zero_iff_two`, `_three`, `_four`).

What this does not say: nothing here connects the margins to the Laplace integral. That step is
the named hypothesis `PositionMargin` of `Zoo/TemplateMargin.lean`.
(`VectorSLT` is not written in the `module` system, so this file is a plain, non-`module` file.)
-/

namespace SLT.Zoo.LeadingMaps

open VectorSLT

/-- A real linear form `a s + b t`, read as a complex one. -/
def formC (l : LeadingMap.Form) : PositionFour.Form := ((l.1 : ℂ), (l.2 : ℂ))

/-- A real position-four row (three forms), read as a complex one. -/
def rowC (r : LeadingMap.Row) : PositionFour.Row := fun i => formC (r i)

/-- A real position-two row (one prefix form, two suffix forms), read as a complex one. -/
def row2C (r : LeadingMap.Row2) : MiddlePositions.Row2 := (formC r.1, (formC r.2.1, formC r.2.2))

/-- A real position-three row (two prefix forms, one suffix form), read as a complex one. -/
def row3C (r : LeadingMap.Row3) : MiddlePositions.Row3 := ((formC r.1.1, formC r.1.2), formC r.2)

/-- The cube of a form commutes with complexification. -/
theorem cube_formC (l : LeadingMap.Form) (i : Fin 4) :
    PositionFour.cube (formC l) i = ((LeadingMap.cube l i : ℝ) : ℂ) := by
  fin_cases i <;> simp [PositionFour.cube, LeadingMap.cube, formC]

/-- The sum of two cubes commutes with complexification. -/
theorem twoCube_formC (g : LeadingMap.Form × LeadingMap.Form) (i : Fin 4) :
    PositionFour.twoCube (formC g.1, formC g.2) i = ((LeadingMap.twoCube g i : ℝ) : ℂ) := by
  simp [PositionFour.twoCube, LeadingMap.twoCube, cube_formC]

/-- The row cubic commutes with complexification. -/
theorem rowCubic_rowC (r : LeadingMap.Row) (i : Fin 4) :
    PositionFour.rowCubic (rowC r) i = ((LeadingMap.rowCubic r i : ℝ) : ℂ) := by
  simp [PositionFour.rowCubic, LeadingMap.rowCubic, rowC, cube_formC, Finset.sum_apply]

/-- **Position two.** The core's `R2` on real inputs is the complexification of the network
library's `R2`. -/
theorem R2_complexify (w : LeadingMap.Row2 × LeadingMap.Row2) (i : Fin 11) :
    MiddlePositions.R2 (row2C w.1, row2C w.2) i = ((LeadingMap.R2 w i : ℝ) : ℂ) := by
  fin_cases i <;>
    simp [MiddlePositions.R2, MiddlePositions.generators, LeadingMap.R2, LeadingMap.generators,
      row2C, cube_formC, twoCube_formC]

/-- **Position three.** The core's `R3` on real inputs is the complexification of the network
library's `R3`. -/
theorem R3_complexify (w : LeadingMap.Row3 × LeadingMap.Row3) (i : Fin 11) :
    MiddlePositions.R3 (row3C w.1, row3C w.2) i = ((LeadingMap.R3 w i : ℝ) : ℂ) := by
  fin_cases i <;>
    simp [MiddlePositions.R3, MiddlePositions.generators, LeadingMap.R3, LeadingMap.generators,
      row3C, cube_formC, twoCube_formC]

/-- **Position four.** The core's `leadingMap` on real inputs is the complexification of the
network library's `leadingMap`. -/
theorem leadingMap_complexify (w : LeadingMap.Row × LeadingMap.Row) (i : Fin 6) :
    PositionFour.leadingMap (rowC w.1, rowC w.2) i = ((LeadingMap.leadingMap w i : ℝ) : ℂ) := by
  fin_cases i <;>
    simp [PositionFour.leadingMap, LeadingMap.leadingMap, rowCubic_rowC]

/-- A complex vector that is the complexification of a real one vanishes exactly when the real
one does. -/
theorem eq_zero_iff_of_complexify {n : ℕ} {z : Fin n → ℂ} {r : Fin n → ℝ}
    (h : ∀ i, z i = ((r i : ℝ) : ℂ)) : z = 0 ↔ r = 0 := by
  constructor
  · intro hz
    funext i
    have := congrFun hz i
    rw [h i] at this
    simpa using this
  · intro hr
    funext i
    rw [h i, hr]
    simp

/-- **Position two** (Lean `p = 1`): the `ε³` term of the network error vanishes exactly when
the active coordinates and the core's complex leading map `R2` vanish. -/
theorem lead_eq_zero_iff_two (Δ : Matrix (Fin 2) (Fin 2) ℝ)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) :
    LeadingMap.lead A0 1 Δ V = 0 ↔ LeadingMap.activeCoords Δ V = 0 ∧
      MiddlePositions.R2 (row2C (LeadingMap.w2 V).1, row2C (LeadingMap.w2 V).2) = 0 := by
  rw [(LeadingMap.lead_A0_eq_zero_iff Δ V).1,
    eq_zero_iff_of_complexify (R2_complexify (LeadingMap.w2 V))]

/-- **Position three** (Lean `p = 2`): the same with the core's `R3`. -/
theorem lead_eq_zero_iff_three (Δ : Matrix (Fin 2) (Fin 2) ℝ)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) :
    LeadingMap.lead A0 2 Δ V = 0 ↔ LeadingMap.activeCoords Δ V = 0 ∧
      MiddlePositions.R3 (row3C (LeadingMap.w3 V).1, row3C (LeadingMap.w3 V).2) = 0 := by
  rw [(LeadingMap.lead_A0_eq_zero_iff Δ V).2.1,
    eq_zero_iff_of_complexify (R3_complexify (LeadingMap.w3 V))]

/-- **Position four** (Lean `p = 3`): the same with the core's `leadingMap`. -/
theorem lead_eq_zero_iff_four (Δ : Matrix (Fin 2) (Fin 2) ℝ)
    (V : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) :
    LeadingMap.lead A0 3 Δ V = 0 ↔ LeadingMap.activeCoords Δ V = 0 ∧
      PositionFour.leadingMap (rowC (LeadingMap.w4 V).1, rowC (LeadingMap.w4 V).2) = 0 := by
  rw [(LeadingMap.lead_A0_eq_zero_iff Δ V).2.2,
    eq_zero_iff_of_complexify (leadingMap_complexify (LeadingMap.w4 V))]

end SLT.Zoo.LeadingMaps
