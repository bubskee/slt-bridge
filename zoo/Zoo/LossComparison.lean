/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
import VectorSLT
import SLT
import Zoo.TemplateMargin
import Zoo.LeadingMaps

/-!
# Zoo: the position table from three inactive Laplace bounds

`Zoo/TemplateMargin.lean` derives the upper bounds at positions two to four of the depth-four
shear network (`ThmN`, `ThmKUpper`) from the named hypothesis `PositionMargin`. That hypothesis
packages two things: the elementary loss comparison in coordinates `(𝐜, w)`, and the angular
margin of the inactive function.

`vector-slt-lean` (`VectorSLT/LossCompare`) now proves the first of the two, for every shear
target, with explicit inactive polynomials `G₂ = Gmid 1`, `G₃ = Gmid 2`, `G₄ = G4` on `ℝ¹²`:
`κ (‖𝐜‖² + G_p(w)) ≤ K` in coordinates with a bounded change of variables.

This file puts the two libraries together. The active coordinates integrate to a Gaussian factor
`N⁻²`, so all that is left is `InactiveLaplace G_p`: on some ball around the origin of `ℝ¹²`,
`∫ e^{-N G_p} ≤ C N⁻²`. It is a statement about three explicit polynomials and mentions no
network, target, input law, prior or cutoff.

* `Zpos_upper_of_marginData`: `Z_N ≤ C N⁻⁴` from the loss comparison and the inactive bound.
* `thmN_of_inactiveLaplace`, `thmKUpper_of_inactiveLaplace`: the two named hypotheses of
  `vector-slt-lean`, for a shear target and cutoffs supported in a small ball.
* `mainTheorem_shear_of_inactiveLaplace`: the position table `(4,5), (4,1), (4,1), (4,1)` with
  the three inactive bounds as its only hypotheses beyond those of position one.
* `inactiveLaplace_of_angularMargin`, `mainTheorem_shear_of_shellMargin`: the angular margin of
  the template, `ShellMargin H_p` for the angular parts `H₂ = Hmid 1`, `H₃ = Hmid 2`, `H₄ = H4`
  (`G_p(r ξ) = r⁶ H_p(r, ξ)`), is a sufficient condition for the inactive bound.
* `H4_zero_eq_core`, `Hmid_one_zero_eq_core`, `Hmid_two_zero_eq_core`: at `r = 0`, `H_p` is the
  squared norm of the core's complex leading map (`PositionFour.leadingMap`,
  `MiddlePositions.R2`, `R3`) at the real point `ξ`.

What this does not say: the inactive bounds are not proved here. The core proves strict complex
margins for the three leading maps (`SLT.Pushforward.strictShellMargin_leadingMaps`). The paper
goes from those to `InactiveLaplace G_p` in two steps that are not formalized: the stability
theorem of Phong and Sturm gives the bound `N⁻⁴` for the complexified integral over a polydisk of
`ℂ¹²`, and a complex-to-real transfer through a resolution of singularities gives `N⁻²` over
`ℝ¹²`. That argument does not prove `ShellMargin H_p`, which asks for a real bound uniform in the
radius and is the stronger statement.
(`VectorSLT` is not written in the `module` system, so this file is a plain, non-`module` file.)
-/

namespace SLT.Zoo.LossComparison

open MeasureTheory Set Filter Metric Topology VectorSLT SLT.Template SLT.Zoo.TemplateMargin
open scoped ENNReal

/-! ### The inactive Laplace bound -/

/-- **The inactive Laplace bound (named hypothesis).** On some ball around the origin of `ℝ¹²`
the Laplace integral of `G` has upper rate `(2, 1)`: `∫_{‖w‖ ≤ ε/2} e^{-N G(w)} dw ≤ C N⁻²` for
large `N`. -/
def InactiveLaplace (G : (Fin 12 → ℝ) → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    SLT.LaplaceUpper (SLT.Z (volume.restrict (closedBall (0 : Fin 12 → ℝ) (ε / 2))) G) 2 1

/-- The model integral of the margin template is the Gaussian factor of the active coordinates
times the Laplace integral of `G` on the ball. -/
theorem marginModel_eq_mul {a : ℕ} {G : (Fin 12 → ℝ) → ℝ} (hG : Measurable G) (ε N : ℝ) :
    marginModel (a := a) G ε N =
      (∫⁻ u : Fin a → ℝ, ENNReal.ofReal (Real.exp (-(N * ∑ i, u i ^ 2)))) *
        SLT.Z (volume.restrict (closedBall (0 : Fin 12 → ℝ) (ε / 2))) G N := by
  unfold marginModel SLT.Z
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hm1 : Measurable fun u : Fin a → ℝ => ENNReal.ofReal (Real.exp (-(N * ∑ i, u i ^ 2))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((measurable_const.mul
      (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2)).neg))
  have hm2 : Measurable fun w : Fin 12 → ℝ => ENNReal.ofReal (Real.exp (-(N * G w))) := by
    fun_prop
  rw [← lintegral_prod_mul hm1.aemeasurable hm2.aemeasurable]
  refine lintegral_congr fun y => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2; ring

/-- With four active coordinates, the model integral has upper rate `(4, 1)` when the inactive
integral has upper rate `(2, 1)`. -/
theorem marginModel_laplaceUpper_of_inactive {G : (Fin 12 → ℝ) → ℝ} (hG : Measurable G) {ε : ℝ}
    (h : SLT.LaplaceUpper (SLT.Z (volume.restrict (closedBall (0 : Fin 12 → ℝ) (ε / 2))) G) 2 1) :
    SLT.LaplaceUpper (fun N => marginModel (a := 4) G ε N) 4 1 := by
  obtain ⟨C, hC⟩ := h
  refine ⟨Real.pi ^ 2 * C, ?_⟩
  filter_upwards [hC, eventually_gt_atTop 0] with N hN hN0
  rw [marginModel_eq_mul hG, lintegral_exp_neg_sum_sq 4 hN0]
  refine (mul_le_mul' le_rfl hN).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [rate, Nat.sub_self, pow_zero, mul_one]
  have h4 : √(Real.pi / N) ^ 4 = Real.pi ^ 2 * (N ^ 2)⁻¹ := by
    have hsq : √(Real.pi / N) ^ 2 = Real.pi / N := Real.sq_sqrt (by positivity)
    calc √(Real.pi / N) ^ 4 = (√(Real.pi / N) ^ 2) ^ 2 := by ring
      _ = Real.pi ^ 2 * (N ^ 2)⁻¹ := by rw [hsq, div_pow, div_eq_mul_inv]
  have e2 : N ^ (-(2 : ℝ)) = (N ^ 2)⁻¹ := by rw [Real.rpow_neg hN0.le, Real.rpow_two]
  have e4 : N ^ (-(4 : ℝ)) = (N ^ 4)⁻¹ := by
    rw [Real.rpow_neg hN0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h4, e2, e4]
  ring

/-- **The upper bound at a position** from the loss comparison (`MarginData`, proved in
`vector-slt-lean`) and the inactive Laplace bound on the same ball: `Z_{N,p+1} ≤ C N⁻⁴`. -/
theorem Zpos_upper_of_marginData {μ : Measure (Fin 2 → ℝ)} {A : Matrix (Fin 2) (Fin 2) ℝ}
    {φ χ : Raw16 → ℝ≥0∞} {p : Fin 4} {G : (Fin 12 → ℝ) → ℝ} {ε : ℝ} (hG : Measurable G)
    (hL : SLT.LaplaceUpper (SLT.Z (volume.restrict (closedBall (0 : Fin 12 → ℝ) (ε / 2))) G) 2 1)
    (h : LossCompare.MarginData μ A φ χ p G ε) :
    ∃ C N₀ : ℝ, ∀ N, N₀ ≤ N → Zpos μ A φ χ p N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4) := by
  obtain ⟨Ψ, J, κ, -, hκ, hJ, hcmp⟩ := h
  have hup : SLT.LaplaceUpper (Zpos μ A φ χ p) 4 1 :=
    (((marginModel_laplaceUpper_of_inactive hG hL).comp_mul hκ).const_mul
      (a := ENNReal.ofReal J) ENNReal.ofReal_ne_top).mono
      (by filter_upwards [eventually_ge_atTop 0] with N hN
          exact Zpos_le_marginModel hG hJ hcmp hN)
  obtain ⟨C, N₀, hC⟩ := SLT.laplaceUpper_iff.mp hup
  refine ⟨C, max N₀ 1, fun N hN => ?_⟩
  have hN0 : 0 < N := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hN)
  have hb := hC N ((le_max_left _ _).trans hN)
  rw [Real.rpow_neg hN0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← inv_pow] at hb
  simpa using hb

/-- **Positions two and three** (Lean `p = 1, 2`): for a shear target, the inactive Laplace bound
for `G_p` gives `Z_{N,p+1} ≤ C N⁻⁴` for every cutoff supported in a ball of radius `r₀`. -/
theorem Zpos_upper_middle {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) {p : Fin 4}
    (hp : p = 1 ∨ p = 2) (hL : InactiveLaplace (LossCompare.Gmid p)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 ≤ r → r ≤ r₀ →
      ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ℝ≥0∞) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ C N₀ : ℝ, ∀ N, N₀ ≤ N → Zpos μ A φ χ p N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4) := by
  obtain ⟨ε, hε, hup⟩ := hL
  obtain ⟨c, hc, k⟩ := LossCompare.middle_marginData hA hp
  refine ⟨c * min (1 / 2) (ε / 2), mul_pos hc (lt_min (by norm_num) (by linarith)), ?_⟩
  intro r hr0 hr μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ π₁ hπ₁ hφ hχ hχs
  exact Zpos_upper_of_marginData (LossCompare.measurable_Gmid p) hup
    (k ε r hr0 hr μ hmom hlh hμ₀ hμ φ χ hπ₁ hφ hχ hχs)

/-- **Position four** (Lean `p = 3`): for a shear target, the inactive Laplace bound for `G₄`
gives `Z_{N,4} ≤ C N⁻⁴` for every cutoff supported in a ball of radius `r₀`. -/
theorem Zpos_upper_four {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A)
    (hL : InactiveLaplace LossCompare.G4) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 ≤ r → r ≤ r₀ →
      ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ℝ≥0∞) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ∃ C N₀ : ℝ, ∀ N, N₀ ≤ N → Zpos μ A φ χ 3 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4) := by
  obtain ⟨ε, hε, hup⟩ := hL
  obtain ⟨c, hc, k⟩ := LossCompare.position_four_marginData hA
  refine ⟨c * min (1 / 2) (ε / 2), mul_pos hc (lt_min (by norm_num) (by linarith)), ?_⟩
  intro r hr0 hr μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ π₁ hπ₁ hφ hχ hχs
  exact Zpos_upper_of_marginData LossCompare.measurable_G4 hup
    (k ε r hr0 hr μ hmom hlh hμ₀ hμ φ χ hπ₁ hφ hχ hχs)

/-- **`ThmN` from two inactive Laplace bounds.** For a shear target, the bounds for `G₂` and `G₃`
give `Z_{N,2}, Z_{N,3} ≤ C N⁻⁴` for every cutoff supported in a ball of radius `r₀`. -/
theorem thmN_of_inactiveLaplace {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A)
    (h2 : InactiveLaplace (LossCompare.Gmid 1)) (h3 : InactiveLaplace (LossCompare.Gmid 2)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 ≤ r → r ≤ r₀ →
      ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ℝ≥0∞) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) → ThmN μ A φ χ := by
  obtain ⟨r2, hr2, k2⟩ := Zpos_upper_middle hA (Or.inl rfl) h2
  obtain ⟨r3, hr3, k3⟩ := Zpos_upper_middle hA (Or.inr rfl) h3
  refine ⟨min r2 r3, lt_min hr2 hr3, ?_⟩
  intro r hr0 hr μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ π₁ hπ₁ hφ hχ hχs p hp
  rcases hp with rfl | rfl
  · exact k2 r hr0 (hr.trans (min_le_left _ _)) μ hmom hlh hμ₀ hμ φ χ hπ₁ hφ hχ hχs
  · exact k3 r hr0 (hr.trans (min_le_right _ _)) μ hmom hlh hμ₀ hμ φ χ hπ₁ hφ hχ hχs

/-- **`ThmKUpper` from one inactive Laplace bound.** For a shear target, the bound for `G₄` gives
`Z_{N,4} ≤ C N⁻⁴` for every cutoff supported in a ball of radius `r₀`. -/
theorem thmKUpper_of_inactiveLaplace {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A)
    (h4 : InactiveLaplace LossCompare.G4) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 ≤ r → r ≤ r₀ →
      ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ℝ≥0∞) {π₁ : ℝ}, 0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) → ThmKUpper μ A φ χ :=
  Zpos_upper_four hA h4

/-- `ThmK` from its upper half and the proved lower bound `Zpos_lower_N4`. -/
theorem thmK_of_upper {μ : Measure (Fin 2 → ℝ)} [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {A : Matrix (Fin 2) (Fin 2) ℝ} {φ χ : Raw16 → ℝ≥0∞} {φ₀ χ₀ : ℝ} (hφ₀ : 0 < φ₀)
    (hχ₀ : 0 < χ₀) (hφ : ∀ᶠ θ in 𝓝 (basePos A 3), ENNReal.ofReal φ₀ ≤ φ θ)
    (hχ : ∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) (h : ThmKUpper μ A φ χ) : ThmK μ A φ χ := by
  obtain ⟨c, hc, N₁, hlo⟩ := Zpos_lower_N4 μ hmom A 3 φ χ hφ₀ hχ₀ hφ hχ
  obtain ⟨C, N₂, hhi⟩ := h
  exact ⟨c, C, max N₁ N₂, hc, fun N hN =>
    ⟨hlo N ((le_max_left _ _).trans hN), hhi N ((le_max_right _ _).trans hN)⟩⟩

/-- **The position table from three inactive Laplace bounds.** The source's `mainTheorem_shear`,
with `ThmK` and `ThmN` replaced by the Laplace bounds `∫ e^{-N G_p} ≤ C N⁻²` for the explicit
polynomials `G₂`, `G₃`, `G₄` on a ball of `ℝ¹²`. The three hypotheses mention no target, input
law, prior or cutoff. -/
theorem mainTheorem_shear_of_inactiveLaplace (h2 : InactiveLaplace (LossCompare.Gmid 1))
    (h3 : InactiveLaplace (LossCompare.Gmid 2)) (h4 : InactiveLaplace LossCompare.G4)
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
  obtain ⟨r0, hr0, k0⟩ := mainTheorem_shear hA
  obtain ⟨rN, hrN, kN⟩ := thmN_of_inactiveLaplace hA h2 h3
  obtain ⟨rK, hrK, kK⟩ := thmKUpper_of_inactiveLaplace hA h4
  refine ⟨min r0 (min rN rK), lt_min hr0 (lt_min hrN hrK), ?_⟩
  intro μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ φ₀ χ₀ π₁ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs
  set r := min r0 (min rN rK) with hr
  have hrpos : 0 ≤ r := (lt_min hr0 (lt_min hrN hrK)).le
  have hN' : r ≤ rN := (min_le_right _ _).trans (min_le_left _ _)
  have hK' : r ≤ rK := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨p0, p1, p2, p3⟩ := k0 μ hmom hlh hμ₀ hμ φ χ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ
    (fun θ hθ => hχs θ (lt_of_le_of_lt (min_le_left _ _) hθ))
    (thmK_of_upper hmom hφ₀ hχ₀ (hφl 3) hχl
      (kK r hrpos hK' μ hmom hlh hμ₀ hμ φ χ hπ₁ hφ hχ hχs))
    (kN r hrpos hN' μ hmom hlh hμ₀ hμ φ χ hπ₁ hφ hχ hχs)
  exact ⟨VectorShear.ofVector p0 (by norm_num), VectorShear.ofVector p1 le_rfl,
    VectorShear.ofVector p2 le_rfl, VectorShear.ofVector p3 le_rfl⟩

/-! ### A sufficient condition: the angular margin on the shell -/

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

/-- The angular margin with `s > 2` gives the inactive Laplace bound (the radial split of the
margin template, with `D = 12` and `d = 3`). -/
theorem inactiveLaplace_of_angularMargin {G : (Fin 12 → ℝ) → ℝ} (hG : Measurable G) {s ε M : ℝ}
    (hs : 2 < s) (hε : 0 < ε) (hM : 0 ≤ M) (hA : AngularMargin G 3 s ε M) :
    InactiveLaplace G := by
  refine ⟨ε, hε, marginConst 12 3 s M, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with N hN
  have h := lintegral_exp_le_of_angularMargin (D := 12) (d := 3) (by norm_num) (by norm_num) hG
    (by linarith) hM (by push_cast; linarith) hA hN
  refine h.trans (le_of_eq ?_)
  simp only [rate, Nat.sub_self, pow_zero, mul_one]
  norm_num

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

/-- The shell margin of `H₄` gives the inactive Laplace bound for `G₄`. -/
theorem inactiveLaplace_G4_of_shellMargin (h : ShellMargin LossCompare.H4) :
    InactiveLaplace LossCompare.G4 := by
  obtain ⟨s, ε, M, hs, hε, hM, hm⟩ := h
  exact inactiveLaplace_of_angularMargin LossCompare.measurable_G4 hs hε hM (angularMargin_G4 hm)

/-- The shell margin of `H_p` gives the inactive Laplace bound for `G_p` (Lean `p = 1, 2`). -/
theorem inactiveLaplace_Gmid_of_shellMargin {p : Fin 4} (hp : p = 1 ∨ p = 2)
    (h : ShellMargin (LossCompare.Hmid p)) : InactiveLaplace (LossCompare.Gmid p) := by
  obtain ⟨s, ε, M, hs, hε, hM, hm⟩ := h
  exact inactiveLaplace_of_angularMargin (LossCompare.measurable_Gmid p) hs hε hM
    (angularMargin_Gmid hp hm)

/-- **The position table from three shell margins**, a corollary of
`mainTheorem_shear_of_inactiveLaplace`. -/
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
        SLT.HasLaplacePair (Zpos μ A φ χ 2) 4 1 ∧ SLT.HasLaplacePair (Zpos μ A φ χ 3) 4 1 :=
  mainTheorem_shear_of_inactiveLaplace (inactiveLaplace_Gmid_of_shellMargin (Or.inl rfl) h2)
    (inactiveLaplace_Gmid_of_shellMargin (Or.inr rfl) h3) (inactiveLaplace_G4_of_shellMargin h4)
    hA

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
