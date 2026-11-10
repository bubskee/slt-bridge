/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
import VectorSLT
import SLT
import Zoo.VectorShear

/-!
# Zoo: `ThmK` and `ThmN` as instances of the margin template (brief 03, T2 guardrail)

`vector-slt-lean` proves the position table `(4,5), (4,1), (4,1), (4,1)` of the depth-four shear
network with the upper halves at positions two to four taken as the named hypotheses `ThmK`
(position four) and `ThmN` (positions two and three). Each is `Z_{N,j} ≤ C N⁻⁴`.

This file shows both are **instances of the core margin template** (`SLT/Template/Margin.lean`).
`PositionMargin μ A φ χ p` packages, at position `p`, exactly the inputs of cubic-chaos
Theorem K §§1, 6 / Proposition N2:

* coordinates `Ψ θ = (u, w)`: 4 regular active coordinates `u` and 12 inactive ones `w`, with a
  bounded change of variables against the prior × cutoff (the implicit-function step (K3));
* the comparison `κ (|u|² + G(w)) ≤ K(θ)` on the support, with `w` in a small ball;
* the **named hypothesis** `AngularMargin G 3 s ε M` with `s > 2`, i.e. `6s > 12`. The inactive map
  is weighted homogeneous of degree three, and its angular part has a strict margin above 4.

The template's radial split and Gaussian factor give `N^{-(4/2 + 12/6)} = N⁻⁴`, which is `ThmN`
and `ThmKUpper`. With the proved lower bound (`Zpos_lower_N4`) it gives `ThmK`.
`mainTheorem_shear_of_margin` is the source's main theorem with `ThmK` and `ThmN` replaced by the
three position margins.

The implicit-function step is elementary but is not proved here; it is part of `PositionMargin`.
The angular margin is the step that needs resolution and stability (see the project plan, kept outside this repository).
(`VectorSLT` is not written in the `module` system, so this file is a plain, non-`module` file.)
-/

namespace SLT.Zoo.TemplateMargin

open MeasureTheory Set Filter Metric Topology VectorSLT SLT.Template
open scoped ENNReal

/-- **The margin hypotheses at position `p`** of the depth-four network: regular active
coordinates (4) and inactive coordinates (12) with a bounded change of variables against the
prior × cutoff, the loss comparison on its support, and the angular margin of the inactive map
with `s > 2`. -/
def PositionMargin (μ : Measure (Fin 2 → ℝ)) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (φ χ : Raw16 → ℝ≥0∞) (p : Fin 4) : Prop :=
  ∃ (Ψ : Raw16 → (Fin 4 → ℝ) × (Fin 12 → ℝ)) (G : (Fin 12 → ℝ) → ℝ) (J κ s ε M : ℝ),
    Measurable Ψ ∧ Measurable G ∧ 0 < κ ∧ 2 < s ∧ 0 ≤ M ∧ AngularMargin G 3 s ε M ∧
    (∀ f : (Fin 4 → ℝ) × (Fin 12 → ℝ) → ℝ≥0∞, Measurable f →
      ∫⁻ θ, f (Ψ θ) * (φ θ * χ (θ - basePos A p)) ≤ ENNReal.ofReal J * ∫⁻ y, f y) ∧
    ∀ θ, φ θ * χ (θ - basePos A p) ≠ 0 →
      κ * (∑ i, (Ψ θ).1 i ^ 2 + G (Ψ θ).2) ≤ popLossA μ A θ ∧
        (Ψ θ).2 ∈ closedBall (0 : Fin 12 → ℝ) (ε / 2)

/-- The comparison with the template's model integral. -/
theorem Zpos_le_marginModel {μ : Measure (Fin 2 → ℝ)} {A : Matrix (Fin 2) (Fin 2) ℝ}
    {φ χ : Raw16 → ℝ≥0∞} {p : Fin 4} {Ψ : Raw16 → (Fin 4 → ℝ) × (Fin 12 → ℝ)}
    {G : (Fin 12 → ℝ) → ℝ} {J κ ε : ℝ} (hG : Measurable G)
    (hJ : ∀ f : (Fin 4 → ℝ) × (Fin 12 → ℝ) → ℝ≥0∞, Measurable f →
      ∫⁻ θ, f (Ψ θ) * (φ θ * χ (θ - basePos A p)) ≤ ENNReal.ofReal J * ∫⁻ y, f y)
    (hcmp : ∀ θ, φ θ * χ (θ - basePos A p) ≠ 0 →
      κ * (∑ i, (Ψ θ).1 i ^ 2 + G (Ψ θ).2) ≤ popLossA μ A θ ∧
        (Ψ θ).2 ∈ closedBall (0 : Fin 12 → ℝ) (ε / 2))
    {N : ℝ} (hN : 0 ≤ N) :
    Zpos μ A φ χ p N ≤ ENNReal.ofReal J * marginModel (a := 4) G ε (κ * N) := by
  set S : Set ((Fin 4 → ℝ) × (Fin 12 → ℝ)) := univ ×ˢ closedBall (0 : Fin 12 → ℝ) (ε / 2)
  have hS : MeasurableSet S := MeasurableSet.univ.prod isClosed_closedBall.measurableSet
  set f : (Fin 4 → ℝ) × (Fin 12 → ℝ) → ℝ≥0∞ := S.indicator fun y =>
    ENNReal.ofReal (Real.exp (-((κ * N) * (∑ i, y.1 i ^ 2 + G y.2))))
  have hf : Measurable f := by
    refine Measurable.indicator ?_ hS
    have : Measurable fun y : (Fin 4 → ℝ) × (Fin 12 → ℝ) => ∑ i, y.1 i ^ 2 :=
      Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp measurable_fst).pow_const 2
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_const.mul (this.add (hG.comp measurable_snd))).neg))
  calc Zpos μ A φ χ p N
      = ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * popLossA μ A θ))) *
          (φ θ * χ (θ - basePos A p)) := rfl
    _ ≤ ∫⁻ θ, f (Ψ θ) * (φ θ * χ (θ - basePos A p)) := by
        refine lintegral_mono fun θ => ?_
        by_cases h0 : φ θ * χ (θ - basePos A p) = 0
        · rw [h0, mul_zero, mul_zero]
        · obtain ⟨hK, hball⟩ := hcmp θ h0
          refine mul_le_mul' ?_ le_rfl
          simp only [f]; rw [indicator_of_mem (show Ψ θ ∈ S from ⟨mem_univ _, hball⟩)]
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          have := mul_le_mul_of_nonneg_left hK hN
          nlinarith
    _ ≤ ENNReal.ofReal J * ∫⁻ y, f y := hJ f hf
    _ = ENNReal.ofReal J * marginModel (a := 4) G ε (κ * N) := by
        rw [lintegral_indicator hS]; rfl

/-- **The template at position `p`**: `Z_{N,p+1} ≤ C N⁻⁴` from the margin hypotheses. -/
theorem Zpos_upper_of_margin {μ : Measure (Fin 2 → ℝ)} {A : Matrix (Fin 2) (Fin 2) ℝ}
    {φ χ : Raw16 → ℝ≥0∞} {p : Fin 4} (h : PositionMargin μ A φ χ p) :
    ∃ C N₀ : ℝ, ∀ N, N₀ ≤ N → Zpos μ A φ χ p N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4) := by
  obtain ⟨Ψ, G, J, κ, s, ε, M, -, hG, hκ, hs, hM, hA, hJ, hcmp⟩ := h
  have hup := laplaceUpper_of_angularMargin (Z := Zpos μ A φ χ p) (a := 4) (D := 12) (d := 3)
    (by norm_num) (by norm_num) hG (P := ENNReal.ofReal J) ENNReal.ofReal_ne_top hκ
    (by linarith) hM (by push_cast; linarith) hA
    (by filter_upwards [eventually_ge_atTop 0] with N hN
        exact Zpos_le_marginModel hG hJ hcmp hN)
  have e : ((4 : ℕ) : ℝ) / 2 + ((12 : ℕ) : ℝ) / (2 * ((3 : ℕ) : ℝ)) = 4 := by norm_num
  rw [e] at hup
  obtain ⟨C, N₀, hC⟩ := SLT.laplaceUpper_iff.mp hup
  refine ⟨C, max N₀ 1, fun N hN => ?_⟩
  have hN0 : 0 < N := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hN)
  have hb := hC N ((le_max_left _ _).trans hN)
  rw [Real.rpow_neg hN0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← inv_pow] at hb
  simpa using hb

/-- **`ThmN` is an instance of the margin template**: margins at positions two and three. -/
theorem thmN_of_margin {μ : Measure (Fin 2 → ℝ)} {A : Matrix (Fin 2) (Fin 2) ℝ}
    {φ χ : Raw16 → ℝ≥0∞} (h1 : PositionMargin μ A φ χ 1) (h2 : PositionMargin μ A φ χ 2) :
    ThmN μ A φ χ := by
  intro p hp
  rcases hp with rfl | rfl
  · exact Zpos_upper_of_margin h1
  · exact Zpos_upper_of_margin h2

/-- **`ThmKUpper` is an instance of the margin template**: the margin at position four. -/
theorem thmKUpper_of_margin {μ : Measure (Fin 2 → ℝ)} {A : Matrix (Fin 2) (Fin 2) ℝ}
    {φ χ : Raw16 → ℝ≥0∞} (h3 : PositionMargin μ A φ χ 3) : ThmKUpper μ A φ χ :=
  Zpos_upper_of_margin h3

/-- **`ThmK` from the margin template** and the proved lower bound `Zpos_lower_N4`. -/
theorem thmK_of_margin {μ : Measure (Fin 2 → ℝ)} [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {A : Matrix (Fin 2) (Fin 2) ℝ} {φ χ : Raw16 → ℝ≥0∞} {φ₀ χ₀ : ℝ} (hφ₀ : 0 < φ₀)
    (hχ₀ : 0 < χ₀) (hφ : ∀ᶠ θ in 𝓝 (basePos A 3), ENNReal.ofReal φ₀ ≤ φ θ)
    (hχ : ∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) (h3 : PositionMargin μ A φ χ 3) :
    ThmK μ A φ χ := by
  obtain ⟨c, hc, N₁, hlo⟩ := Zpos_lower_N4 μ hmom A 3 φ χ hφ₀ hχ₀ hφ hχ
  obtain ⟨C, N₂, hhi⟩ := Zpos_upper_of_margin h3
  exact ⟨c, C, max N₁ N₂, hc, fun N hN =>
    ⟨hlo N ((le_max_left _ _).trans hN), hhi N ((le_max_right _ _).trans hN)⟩⟩

/-- **The position table, with `ThmK` and `ThmN` replaced by the margin template's hypotheses.**
The source's `mainTheorem_shear`, conditional on the margins at positions two to four instead,
stated in the core's pair predicate. -/
theorem mainTheorem_shear_of_margin {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ℝ≥0∞) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ p : Fin 4, ∀ᶠ θ in 𝓝 (basePos A p), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      PositionMargin μ A φ χ 1 → PositionMargin μ A φ χ 2 → PositionMargin μ A φ χ 3 →
      SLT.HasLaplacePair (Zpos μ A φ χ 0) 4 5 ∧ SLT.HasLaplacePair (Zpos μ A φ χ 1) 4 1 ∧
        SLT.HasLaplacePair (Zpos μ A φ χ 2) 4 1 ∧ SLT.HasLaplacePair (Zpos μ A φ χ 3) 4 1 := by
  obtain ⟨r, hr, h⟩ := mainTheorem_shear hA
  refine ⟨r, hr, ?_⟩
  intro μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ φ₀ χ₀ π₁ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs h1 h2 h3
  obtain ⟨p0, p1, p2, p3⟩ := h μ hmom hlh hμ₀ hμ φ χ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs
    (thmK_of_margin hmom hφ₀ hχ₀ (hφl 3) hχl h3) (thmN_of_margin h1 h2)
  exact ⟨VectorShear.ofVector p0 (by norm_num), VectorShear.ofVector p1 le_rfl,
    VectorShear.ofVector p2 le_rfl, VectorShear.ofVector p3 le_rfl⟩

end SLT.Zoo.TemplateMargin
