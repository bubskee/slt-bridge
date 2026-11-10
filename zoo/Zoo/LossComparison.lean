/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
import VectorSLT
import SLT
import Zoo.TemplateMargin
import Zoo.LeadingMaps

/-!
# Zoo: the position table from three shell margins

`Zoo/TemplateMargin.lean` derives the upper bounds at positions two to four of the depth-four
shear network (`ThmN`, `ThmKUpper`) from the named hypothesis `PositionMargin`. That hypothesis
packages two things: the elementary loss comparison in coordinates `(𝐜, w)`, and the angular
margin of the inactive function.

`vector-slt-lean` (`VectorSLT/LossCompare`) now proves the first of the two, for every shear
target, with explicit inactive functions `G₂ = Gmid 1`, `G₃ = Gmid 2`, `G₄ = G4` and angular
parts `H₂ = Hmid 1`, `H₃ = Hmid 2`, `H₄ = H4` (`G_p(r ξ) = r⁶ H_p(r, ξ)`).

This file puts the two libraries together. What is left of `PositionMargin` is `ShellMargin H_p`:
for some `s > 2`, the integral of `H_p(r, ·)^{-s}` over the shell `{1/2 ≤ ‖ξ‖ < 1}` of `ℝ¹²` is
bounded uniformly in small `r > 0`. It is a statement about three explicit polynomials and
mentions no network, target, input law, prior or cutoff.

* `positionMargin_of_shellMargin_middle`, `positionMargin_of_shellMargin_four`: `PositionMargin`
  at a shear target from the shell margin, for cutoffs supported in a small ball.
* `thmN_of_shellMargin`, `thmKUpper_of_shellMargin`: the two named hypotheses of
  `vector-slt-lean`.
* `mainTheorem_shear_of_shellMargin`: the position table `(4,5), (4,1), (4,1), (4,1)` with the
  three shell margins as its only hypotheses beyond those of position one.
* `H4_zero_eq_core`, `Hmid_one_zero_eq_core`, `Hmid_two_zero_eq_core`: at `r = 0`, `H_p` is the
  squared norm of the core's complex leading map (`PositionFour.leadingMap`,
  `MiddlePositions.R2`, `R3`) at the real point `ξ`.

What this does not say: the shell margins are not proved here. The core proves strict complex
margins for the three leading maps (`SLT.Pushforward.strictShellMargin_leadingMaps`). The passage
from those to `ShellMargin H_p`, uniformly in small `r`, uses the stability theorem of Phong and
Sturm and a complex-to-real transfer, which are not formalized.
(`VectorSLT` is not written in the `module` system, so this file is a plain, non-`module` file.)
-/

namespace SLT.Zoo.LossComparison

open MeasureTheory Set Filter Metric Topology VectorSLT SLT.Template SLT.Zoo.TemplateMargin
open scoped ENNReal

/-- **The shell margin** of an angular function `H` on `ℝ × ℝ¹²`: for some `s > 2` and `ε > 0`,
`∫_{shell} H(r, ·)^{-s} ≤ M` for every `0 < r ≤ ε`. -/
def ShellMargin (H : ℝ → (Fin 12 → ℝ) → ℝ) : Prop :=
  ∃ s ε M : ℝ, 2 < s ∧ 0 < ε ∧ 0 ≤ M ∧ ∀ r : ℝ, 0 < r → r ≤ ε →
    ∫⁻ ξ in shell 12, ENNReal.ofReal (H r ξ) ^ (-s) ≤ ENNReal.ofReal M

/-- `PositionMargin` is the loss comparison (`MarginData`) together with the angular margin. -/
theorem positionMargin_of_marginData {μ : Measure (Fin 2 → ℝ)} {A : Matrix (Fin 2) (Fin 2) ℝ}
    {φ χ : Raw16 → ℝ≥0∞} {p : Fin 4} {G : (Fin 12 → ℝ) → ℝ} {s ε M : ℝ} (hG : Measurable G)
    (hs : 2 < s) (hM : 0 ≤ M) (hA : AngularMargin G 3 s ε M)
    (h : LossCompare.MarginData μ A φ χ p G ε) : PositionMargin μ A φ χ p := by
  obtain ⟨Ψ, J, κ, hΨ, hκ, hJ, hcmp⟩ := h
  exact ⟨Ψ, G, J, κ, s, ε, M, hΨ, hG, hκ, hs, hM, hA, hJ, hcmp⟩

/-- The angular margin of `G₄`, from the shell bound for `H₄` alone. -/
theorem angularMargin_G4 {s ε M : ℝ}
    (h : ∀ r : ℝ, 0 < r → r ≤ ε →
      ∫⁻ ξ in shell 12, ENNReal.ofReal (LossCompare.H4 r ξ) ^ (-s) ≤ ENNReal.ofReal M) :
    AngularMargin LossCompare.G4 3 s ε M :=
  ⟨LossCompare.H4, fun r _ _ ξ _ => ⟨LossCompare.G4_smul r ξ, LossCompare.H4_nonneg r ξ⟩, h⟩

/-- The angular margin of `G₂`, `G₃` (Lean `p = 1, 2`), from the shell bound for `H_p` alone. -/
theorem angularMargin_Gmid {p : Fin 4} (hp : p = 1 ∨ p = 2) {s ε M : ℝ}
    (h : ∀ r : ℝ, 0 < r → r ≤ ε →
      ∫⁻ ξ in shell 12, ENNReal.ofReal (LossCompare.Hmid p r ξ) ^ (-s) ≤ ENNReal.ofReal M) :
    AngularMargin (LossCompare.Gmid p) 3 s ε M :=
  ⟨LossCompare.Hmid p, fun r _ _ ξ _ =>
    ⟨LossCompare.Gmid_smul hp r ξ, LossCompare.Hmid_nonneg p r ξ⟩, h⟩

/-- **Positions two and three** (Lean `p = 1, 2`): for a shear target, the shell margin of `H_p`
gives `PositionMargin` for every cutoff supported in a ball of radius `r₀`. -/
theorem positionMargin_of_shellMargin_middle {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A)
    {p : Fin 4} (hp : p = 1 ∨ p = 2) (hH : ShellMargin (LossCompare.Hmid p)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 ≤ r → r ≤ r₀ →
      ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ℝ≥0∞) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) → PositionMargin μ A φ χ p := by
  obtain ⟨s, ε, M, hs, hε, hM, hm⟩ := hH
  obtain ⟨c, hc, k⟩ := LossCompare.middle_marginData hA hp
  refine ⟨c * min (1 / 2) (ε / 2), mul_pos hc (lt_min (by norm_num) (by linarith)), ?_⟩
  intro r hr0 hr μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ π₁ hπ₁ hφ hχ hχs
  exact positionMargin_of_marginData (LossCompare.measurable_Gmid p) hs hM
    (angularMargin_Gmid hp hm) (k ε r hr0 hr μ hmom hlh hμ₀ hμ φ χ hπ₁ hφ hχ hχs)

/-- **Position four** (Lean `p = 3`): for a shear target, the shell margin of `H₄` gives
`PositionMargin` for every cutoff supported in a ball of radius `r₀`. -/
theorem positionMargin_of_shellMargin_four {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A)
    (hH : ShellMargin LossCompare.H4) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 ≤ r → r ≤ r₀ →
      ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ℝ≥0∞) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) → PositionMargin μ A φ χ 3 := by
  obtain ⟨s, ε, M, hs, hε, hM, hm⟩ := hH
  obtain ⟨c, hc, k⟩ := LossCompare.position_four_marginData hA
  refine ⟨c * min (1 / 2) (ε / 2), mul_pos hc (lt_min (by norm_num) (by linarith)), ?_⟩
  intro r hr0 hr μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ π₁ hπ₁ hφ hχ hχs
  exact positionMargin_of_marginData LossCompare.measurable_G4 hs hM (angularMargin_G4 hm)
    (k ε r hr0 hr μ hmom hlh hμ₀ hμ φ χ hπ₁ hφ hχ hχs)

/-- **`ThmN` from two shell margins.** For a shear target, the shell margins of `H₂` and `H₃` give
`Z_{N,2}, Z_{N,3} ≤ C N⁻⁴` for every cutoff supported in a ball of radius `r₀`. -/
theorem thmN_of_shellMargin {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A)
    (h2 : ShellMargin (LossCompare.Hmid 1)) (h3 : ShellMargin (LossCompare.Hmid 2)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 ≤ r → r ≤ r₀ →
      ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ℝ≥0∞) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) → ThmN μ A φ χ := by
  obtain ⟨r2, hr2, k2⟩ := positionMargin_of_shellMargin_middle hA (Or.inl rfl) h2
  obtain ⟨r3, hr3, k3⟩ := positionMargin_of_shellMargin_middle hA (Or.inr rfl) h3
  refine ⟨min r2 r3, lt_min hr2 hr3, ?_⟩
  intro r hr0 hr μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ π₁ hπ₁ hφ hχ hχs
  exact thmN_of_margin
    (k2 r hr0 (hr.trans (min_le_left _ _)) μ hmom hlh hμ₀ hμ φ χ hπ₁ hφ hχ hχs)
    (k3 r hr0 (hr.trans (min_le_right _ _)) μ hmom hlh hμ₀ hμ φ χ hπ₁ hφ hχ hχs)

/-- **`ThmKUpper` from one shell margin.** For a shear target, the shell margin of `H₄` gives
`Z_{N,4} ≤ C N⁻⁴` for every cutoff supported in a ball of radius `r₀`. -/
theorem thmKUpper_of_shellMargin {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A)
    (h4 : ShellMargin LossCompare.H4) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 ≤ r → r ≤ r₀ →
      ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ℝ≥0∞) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) → ThmKUpper μ A φ χ := by
  obtain ⟨r4, hr4, k4⟩ := positionMargin_of_shellMargin_four hA h4
  refine ⟨r4, hr4, ?_⟩
  intro r hr0 hr μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ π₁ hπ₁ hφ hχ hχs
  exact thmKUpper_of_margin (k4 r hr0 hr μ hmom hlh hμ₀ hμ φ χ hπ₁ hφ hχ hχs)

/-- **The position table from three shell margins.** The source's `mainTheorem_shear`, with
`ThmK` and `ThmN` replaced by the shell margins of the explicit functions `H₂`, `H₃`, `H₄`. The
three hypotheses mention no target, input law, prior or cutoff. -/
theorem mainTheorem_shear_of_shellMargin (h2 : ShellMargin (LossCompare.Hmid 1))
    (h3 : ShellMargin (LossCompare.Hmid 2)) (h4 : ShellMargin LossCompare.H4)
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ℝ≥0∞) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ p : Fin 4, ∀ᶠ θ in 𝓝 (basePos A p), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      SLT.HasLaplacePair (Zpos μ A φ χ 0) 4 5 ∧ SLT.HasLaplacePair (Zpos μ A φ χ 1) 4 1 ∧
        SLT.HasLaplacePair (Zpos μ A φ χ 2) 4 1 ∧ SLT.HasLaplacePair (Zpos μ A φ χ 3) 4 1 := by
  obtain ⟨r0, hr0, k0⟩ := mainTheorem_shear_of_margin hA
  obtain ⟨r2, hr2, k2⟩ := positionMargin_of_shellMargin_middle hA (Or.inl rfl) h2
  obtain ⟨r3, hr3, k3⟩ := positionMargin_of_shellMargin_middle hA (Or.inr rfl) h3
  obtain ⟨r4, hr4, k4⟩ := positionMargin_of_shellMargin_four hA h4
  refine ⟨min (min r0 r2) (min r3 r4), lt_min (lt_min hr0 hr2) (lt_min hr3 hr4), ?_⟩
  intro μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ φ₀ χ₀ π₁ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs
  set r := min (min r0 r2) (min r3 r4) with hr
  have hrpos : 0 ≤ r := (lt_min (lt_min hr0 hr2) (lt_min hr3 hr4)).le
  have h0 : r ≤ r0 := (min_le_left _ _).trans (min_le_left _ _)
  have h2' : r ≤ r2 := (min_le_left _ _).trans (min_le_right _ _)
  have h3' : r ≤ r3 := (min_le_right _ _).trans (min_le_left _ _)
  have h4' : r ≤ r4 := (min_le_right _ _).trans (min_le_right _ _)
  exact k0 μ hmom hlh hμ₀ hμ φ χ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ
    (fun θ hθ => hχs θ (lt_of_le_of_lt h0 hθ))
    (k2 r hrpos h2' μ hmom hlh hμ₀ hμ φ χ hπ₁ hφ hχ hχs)
    (k3 r hrpos h3' μ hmom hlh hμ₀ hμ φ χ hπ₁ hφ hχ hχs)
    (k4 r hrpos h4' μ hmom hlh hμ₀ hμ φ χ hπ₁ hφ hχ hχs)

/-! ### The angular functions at `r = 0` are the core's leading maps -/

/-- The squared modulus of the complexification of a real number is its square. -/
theorem norm_sq_complexify {z : ℂ} {x : ℝ} (h : z = ((x : ℝ) : ℂ)) : ‖z‖ ^ 2 = x ^ 2 := by
  rw [h, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Position four.** `H₄(0, ξ)` is the squared norm of the core's complex `leadingMap` at the
real point `ξ`. -/
theorem H4_zero_eq_core (ξ : Fin 12 → ℝ) :
    LossCompare.H4 0 ξ = ∑ i, ‖PositionFour.leadingMap
      (LeadingMaps.rowC (LeadingMap.w4 (LossCompare.unflat ξ)).1,
        LeadingMaps.rowC (LeadingMap.w4 (LossCompare.unflat ξ)).2) i‖ ^ 2 := by
  rw [LossCompare.H4_zero]
  exact Finset.sum_congr rfl fun i _ =>
    (norm_sq_complexify (LeadingMaps.leadingMap_complexify _ i)).symm

/-- **Position two** (Lean `p = 1`). `H₂(0, ξ)` is the squared norm of the core's complex `R2` at
the real point `ξ`. -/
theorem Hmid_one_zero_eq_core (ξ : Fin 12 → ℝ) :
    LossCompare.Hmid 1 0 ξ = ∑ i, ‖MiddlePositions.R2
      (LeadingMaps.row2C (LeadingMap.w2 (LossCompare.unflat ξ)).1,
        LeadingMaps.row2C (LeadingMap.w2 (LossCompare.unflat ξ)).2) i‖ ^ 2 := by
  rw [LossCompare.Hmid_zero_one]
  exact Finset.sum_congr rfl fun i _ =>
    (norm_sq_complexify (LeadingMaps.R2_complexify _ i)).symm

/-- **Position three** (Lean `p = 2`). `H₃(0, ξ)` is the squared norm of the core's complex `R3`
at the real point `ξ`. -/
theorem Hmid_two_zero_eq_core (ξ : Fin 12 → ℝ) :
    LossCompare.Hmid 2 0 ξ = ∑ i, ‖MiddlePositions.R3
      (LeadingMaps.row3C (LeadingMap.w3 (LossCompare.unflat ξ)).1,
        LeadingMaps.row3C (LeadingMap.w3 (LossCompare.unflat ξ)).2) i‖ ^ 2 := by
  rw [LossCompare.Hmid_zero_two]
  exact Finset.sum_congr rfl fun i _ =>
    (norm_sq_complexify (LeadingMaps.R3_complexify _ i)).symm

end SLT.Zoo.LossComparison
