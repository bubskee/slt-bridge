/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Upstream.RefFibre

/-!
# The complex margin at the middle positions: shared definitions and interface

Source: `forum/complex_middle_positions/complex_middle_positions.tex` (2026-11-09). The note proves,
for the leading maps `R₂` and `R₃` of the two middle positions,
`∫_{‖R_j(w)‖ < 1} ‖w‖^{1/4} dw < ∞` over `ℂ¹²`.

This file is byte-identical on three branches and must not be edited on any of them.

* `mid-toolkit` proves the three interface statements `WeightedTwoCubeBound`,
  `LocallyIntegrableF` and `FullPlaneQuadratic`.
* `mid-two` proves `SublevelTwo` from the interface.
* `mid-three` proves `SublevelThree` from the interface.

Conventions are those of `SLT.PositionFour.Defs`: a form `a s + b t` is `(a, b) : Form`, cubics are
in moment coordinates, and all norms are sup norms.
-/

@[expose] public section

namespace SLT.MiddlePositions

open MeasureTheory SLT.PositionFour
open scoped ENNReal

/-! ### The leading maps -/

/-- The eleven generators of the leading map (Lemma N3 of the paper), in terms of the prefix
cubics `p¹, p²` and the suffix cubics `q¹, q²` of the two rows:
`p^k_2, p^k_3, q^k_2, q^k_3`, then `p¹₁ - p²₁`, `q¹₁ - q²₁` and `p¹₀ - p²₀ + q¹₁`.
The suffix coefficients `q^k_0` do not appear. -/
def generators (p₁ q₁ p₂ q₂ : Cubic) : Fin 11 → ℂ :=
  ![p₁ 2, p₁ 3, q₁ 2, q₁ 3, p₂ 2, p₂ 3, q₂ 2, q₂ 3,
    p₁ 1 - p₂ 1, q₁ 1 - q₂ 1, p₁ 0 - p₂ 0 + q₁ 1]

/-- A row at position two: one prefix form and a pair of suffix forms. -/
abbrev Row2 := Form × (Form × Form)

/-- A row at position three: a pair of prefix forms and one suffix form. -/
abbrev Row3 := (Form × Form) × Form

/-- The leading map at position two, on `Row2 × Row2 ≃ ℂ¹²`. -/
def R2 (w : Row2 × Row2) : Fin 11 → ℂ :=
  generators (cube w.1.1) (twoCube w.1.2) (cube w.2.1) (twoCube w.2.2)

/-- The leading map at position three, on `Row3 × Row3 ≃ ℂ¹²`. -/
def R3 (w : Row3 × Row3) : Fin 11 → ℂ :=
  generators (twoCube w.1.1) (cube w.1.2) (twoCube w.2.1) (cube w.2.2)

/-! ### The headline statements -/

/-- **Theorem (position two).** `∫_{‖R₂ w‖ < 1} ‖w‖^{1/4} dw < ∞`. -/
def SublevelTwo : Prop :=
  ∫⁻ w in {w : Row2 × Row2 | ‖R2 w‖ < 1}, ENNReal.ofReal (‖w‖ ^ (1 / 4 : ℝ)) < ∞

/-- **Theorem (position three).** `∫_{‖R₃ w‖ < 1} ‖w‖^{1/4} dw < ∞`. -/
def SublevelThree : Prop :=
  ∫⁻ w in {w : Row3 × Row3 | ‖R3 w‖ < 1}, ENNReal.ofReal (‖w‖ ^ (1 / 4 : ℝ)) < ∞

/-! ### The interface -/

/-- The weight on a pair of forms: `W₂(g) = 1 + |a|^{1/4} + |b|^{1/4} + |c|^{1/4} + |d|^{1/4}`. -/
noncomputable def W2 (g : Form × Form) : ℝ :=
  1 + ‖g.1.1‖ ^ (1 / 4 : ℝ) + ‖g.1.2‖ ^ (1 / 4 : ℝ) + ‖g.2.1‖ ^ (1 / 4 : ℝ) + ‖g.2.2‖ ^ (1 / 4 : ℝ)

/-- The weight on one form: `W₁(l) = 1 + |a|^{1/4} + |b|^{1/4}`. -/
noncomputable def W1 (l : Form) : ℝ := 1 + ‖l.1‖ ^ (1 / 4 : ℝ) + ‖l.2‖ ^ (1 / 4 : ℝ)

/-- The note's bounding density `F(P) = |𝔇(P)|^{-4/3} + ‖P‖^{1/4} |𝔇(P)|^{-11/8}`, with value `∞`
where `𝔇(P) = 0` (including `P = 0`, through the first summand). -/
noncomputable def F (P : Cubic) : ℝ≥0∞ :=
  twoCubeDensity P + ENNReal.ofReal (‖P‖ ^ (1 / 4 : ℝ)) * ((‖disc P‖₊ : ℝ≥0∞)⁻¹) ^ (11 / 8 : ℝ)

/-- **Interface 1 (the note's Lemma "weighted two-cube measure bound", first half).** The
pushforward of `W₂ · Lebesgue` under the two-cube map is at most `C · F · Lebesgue`. -/
def WeightedTwoCubeBound (C : ℝ) : Prop :=
  ((volume : Measure (Form × Form)).withDensity fun g => ENNReal.ofReal (W2 g)).map twoCube ≤
    ENNReal.ofReal C • (volume : Measure Cubic).withDensity F

/-- **Interface 2 (the same lemma, second half).** `F` is integrable on every closed ball. -/
def LocallyIntegrableF : Prop :=
  ∀ r : ℝ, ∫⁻ P in Metric.closedBall (0 : Cubic) r, F P < ∞

/-- **Interface 3 (the note's Lemma "planar powers and quadratics", last display).** For a
quadratic with `A ≠ 0`, `∫_ℂ |A z² + B z + D|^{-t} ≤ C |A|^{t-2} |B² - 4AD|^{1-t}`. The right side
is `∞` when the discriminant vanishes. It holds with some `C` for every `1 < t < 2`. -/
def FullPlaneQuadratic (t C : ℝ) : Prop :=
  ∀ A B D : ℂ, A ≠ 0 →
    ∫⁻ z : ℂ, ‖A * z ^ 2 + B * z + D‖ₑ⁻¹ ^ t ≤
      ENNReal.ofReal (C * ‖A‖ ^ (t - 2)) * ‖B ^ 2 - 4 * A * D‖ₑ⁻¹ ^ (t - 1)

end SLT.MiddlePositions
