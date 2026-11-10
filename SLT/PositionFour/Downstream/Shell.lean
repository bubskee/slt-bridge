/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Downstream.Finiteness
public import SLT.Pushforward.Shell

/-!
# The angular margin on the shell

The form of the threshold that paper 2 consumes: for every `s < 13/3`,
`‖R(w)‖^{-2s}` is integrable on the shell `{1/2 ≤ ‖w‖ < 1}` of `Row × Row` (sup norm, the library's
shell convention of `SLT/Template/Margin.lean`). This is `shell_lintegral_lt_top` (`ℝ≥0∞` form) and
`integrableOn_shell` (Bochner form), from the weighted sublevel finiteness of Section 3 and cubic
homogeneity `R(c w) = c³ R(w)`.

The note derives it from the exact polar identity
`I_β = (24 + β)⁻¹ ∫_{S²³} ‖R(ω)‖^{-8-β/3} dσ(ω)`. Here only the needed inequality is used, in the
form of the dyadic shell bound `SLT.Pushforward.lintegral_homShell_lt_top_of_moment_24` for any
continuous cubically homogeneous map on a space of real dimension `24`: if
`I_β = ∫_{‖R‖ < 1} ‖w‖^β < ∞` and `6s < 24 + β`, the shell integral is finite. This file supplies
the homogeneity, continuity, dimension and Haar instance for `leadingMap` on `Row × Row`.

Taking `β ∈ (6s - 24, 2)` gives every `s < 13/3`.
-/

@[expose] public section

namespace SLT.PositionFour.Downstream

open MeasureTheory Set Real Metric SLT.Pushforward
open scoped ENNReal NNReal Pointwise

/-! ### Homogeneity and size of the leading map -/

/-- Cubes are cubic: `cube (c l) = c³ cube l`. -/
theorem cube_smul (c : ℝ) (l : Form) : cube (c • l) = (c ^ 3) • cube l := by
  funext i
  fin_cases i <;> simp [cube, Complex.real_smul] <;> ring

/-- The row cubic is cubic: `T (c r) = c³ T r`. -/
theorem rowCubic_smul (c : ℝ) (r : Row) : rowCubic (c • r) = (c ^ 3) • rowCubic r := by
  simp only [rowCubic, Pi.smul_apply, cube_smul, Finset.smul_sum]

/-- **Cubic homogeneity of the leading map**: `R (c w) = c³ R w`. -/
theorem leadingMap_smul (c : ℝ) (w : Row × Row) :
    leadingMap (c • w) = (c ^ 3) • leadingMap w := by
  funext i
  fin_cases i <;>
    simp [leadingMap, Prod.smul_fst, Prod.smul_snd, rowCubic_smul, smul_sub]

/-- `‖R (c w)‖ = |c|³ ‖R w‖`. -/
theorem norm_leadingMap_smul (c : ℝ) (w : Row × Row) :
    ‖leadingMap (c • w)‖ = |c| ^ 3 * ‖leadingMap w‖ := by
  rw [leadingMap_smul, norm_smul, Real.norm_eq_abs, abs_pow]

/-- The leading map is continuous. -/
theorem continuous_leadingMap : Continuous leadingMap := by
  have : Continuous rowCubic := by unfold rowCubic cube; fun_prop
  exact continuous_cubicMap.comp (this.prodMap this)

/-- The raw norm is dominated by the row weights: `‖w‖^β ≤ W_β(w₁) + W_β(w₂)` for `β ≥ 0`. -/
theorem norm_rpow_le_rowWeight {β : ℝ} (hβ : 0 ≤ β) (w : Row × Row) :
    ‖w‖ ^ β ≤ rowWeight β w.1 + rowWeight β w.2 := by
  have hrow : ∀ r : Row, ‖r‖ ^ β ≤ rowWeight β r := by
    intro r
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => ‖r i‖)
      Finset.univ_nonempty
    have hle : ‖r‖ ≤ ‖r j‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => hj i (Finset.mem_univ _)
    calc ‖r‖ ^ β ≤ ‖r j‖ ^ β := Real.rpow_le_rpow (norm_nonneg _) hle hβ
      _ ≤ rowWeight β r := Finset.single_le_sum (f := fun i => ‖r i‖ ^ β)
          (fun i _ => Real.rpow_nonneg (norm_nonneg _) _) (Finset.mem_univ j)
  have h1 := hrow w.1
  have h2 := hrow w.2
  have n1 := rowWeight_nonneg β w.1
  have n2 := rowWeight_nonneg β w.2
  rw [Prod.norm_def]
  rcases le_total ‖w.1‖ ‖w.2‖ with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-! ### Volume on `Row × Row` -/

/-- Lebesgue measure on `Row × Row` is an additive Haar measure. -/
instance isAddHaarMeasure_volume_rowPair :
    (volume : Measure (Row × Row)).IsAddHaarMeasure := by
  have : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have : (volume : Measure Row).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.prod.instIsAddHaarMeasure _ _

/-- `Row × Row` has real dimension `24`. -/
theorem finrank_rowPair : Module.finrank ℝ (Row × Row) = 24 := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype]
  simp [Module.finrank_prod, Complex.finrank_real_complex]

/-! ### The shell -/

/-- The shell `{1/2 ≤ ‖w‖ < 1}` of `Row × Row` (sup norm), as in `SLT.Template.shell`: the shell
`SLT.Pushforward.homShell` of this space. -/
abbrev rowShell : Set (Row × Row) := homShell (Row × Row)

/-- **The shell bound, given the weighted sublevel integral**: if `I_β = ∫_{‖R‖<1} ‖w‖^β` is finite
for some `β ≥ 0` with `2s < 8 + β/3`, then `∫_{shell} ‖R‖^{-2s} < ∞`. The case `R = leadingMap` of
`SLT.Pushforward.lintegral_homShell_lt_top_of_moment_24`. -/
theorem shell_lintegral_lt_top_of_moment {β s : ℝ} (hβ : 0 ≤ β) (hs : 2 * s < 8 + β / 3)
    (hI : ∫⁻ w in {w : Row × Row | ‖leadingMap w‖ < 1}, ENNReal.ofReal (‖w‖ ^ β) < ∞) :
    ∫⁻ w in rowShell, ‖leadingMap w‖ₑ⁻¹ ^ (2 * s) < ∞ :=
  lintegral_homShell_lt_top_of_moment_24 volume continuous_leadingMap
    (fun c hc w => by rw [norm_leadingMap_smul, abs_of_pos hc]) finrank_rowPair hβ hs hI

/-- **The angular margin on the shell** (`ℝ≥0∞` form). Given the density interface at the
weights `0` and `β`, with `0 ≤ β < 2` and `2s < 8 + β/3`:
`∫_{1/2 ≤ ‖w‖ < 1} ‖R(w)‖^{-2s} dw < ∞`. -/
theorem shell_lintegral_lt_top {s β C₀ C : ℝ} (hβ0 : 0 ≤ β) (hβ2 : β < 2)
    (hs : 2 * s < 8 + β / 3) (hD₀ : DensityBound 0 C₀) (hDβ : DensityBound β C)
    (hL₀ : LocallyFiniteRow 0) (hLβ : LocallyFiniteRow β) :
    ∫⁻ w in rowShell, ‖leadingMap w‖ₑ⁻¹ ^ (2 * s) < ∞ := by
  refine shell_lintegral_lt_top_of_moment hβ0 hs (lt_of_le_of_lt ?_
    (sublevel_weighted_lt_top hβ0 hβ2 hD₀ hDβ hL₀ hLβ))
  refine setLIntegral_mono (by
    have h := measurable_rowWeight β
    fun_prop) fun w _ => ENNReal.ofReal_le_ofReal (norm_rpow_le_rowWeight hβ0 w)

/-- **The angular margin for every `s < 13/3`**, given the density interface at every weight
`β ∈ [0, 2)`. The weight used is `β = max 0 ((6s - 22)/2)`. -/
theorem shell_lintegral_lt_top_of_interface {s : ℝ} (hs : s < 13 / 3)
    (h : ∀ β : ℝ, 0 ≤ β → β < 2 → ∃ C, DensityBound β C ∧ LocallyFiniteRow β) :
    ∫⁻ w in rowShell, ‖leadingMap w‖ₑ⁻¹ ^ (2 * s) < ∞ := by
  set β := max 0 ((6 * s - 22) / 2) with hβ
  have hβ0 : 0 ≤ β := le_max_left _ _
  have hβ2 : β < 2 := max_lt (by norm_num) (by linarith)
  have hsβ : 2 * s < 8 + β / 3 := by
    rcases le_total 0 ((6 * s - 22) / 2) with h' | h'
    · rw [hβ, max_eq_right h']; linarith
    · rw [hβ, max_eq_left h']; linarith
  obtain ⟨C₀, hD₀, hL₀⟩ := h 0 le_rfl (by norm_num)
  obtain ⟨C, hD, hL⟩ := h β hβ0 hβ2
  exact shell_lintegral_lt_top hβ0 hβ2 hsβ hD₀ hD hL₀ hL

/-- **The angular margin on the shell** (Bochner form): `‖R‖^{-2s}` is integrable on the shell. -/
theorem integrableOn_shell {s β C₀ C : ℝ} (hβ0 : 0 ≤ β) (hβ2 : β < 2)
    (hs : 2 * s < 8 + β / 3) (hD₀ : DensityBound 0 C₀) (hDβ : DensityBound β C)
    (hL₀ : LocallyFiniteRow 0) (hLβ : LocallyFiniteRow β) :
    IntegrableOn (fun w => ‖leadingMap w‖ ^ (-(2 * s))) rowShell := by
  refine ⟨(continuous_leadingMap.norm.measurable.pow_const _).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun w => ?_)
    (shell_lintegral_lt_top hβ0 hβ2 hs hD₀ hDβ hL₀ hLβ)
  rw [Real.enorm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), ← ofReal_norm]
  exact ofReal_rpow_neg_le (norm_nonneg _) _

end SLT.PositionFour.Downstream
