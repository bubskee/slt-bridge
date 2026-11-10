/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Basic
public import SLT.PositionFour.Downstream.Shell
public import SLT.Pushforward.Shell

/-!
# The shell corollary at the middle positions (note §6)

The dyadic shell bound for any continuous cubically homogeneous map lives in
`SLT.Pushforward.lintegral_homShell_lt_top_of_moment` (`SLT/Pushforward/Shell.lean`). This file
applies it to `R2` on `Row2 × Row2` and `R3` on `Row3 × Row3`: both maps are continuous and cubic
(`norm_R2_smul`, `norm_R3_smul`), both spaces have real dimension `24`, so `SublevelTwo` (resp.
`SublevelThree`), the moment at `β = 1/4`, gives the shell integral for every `s < 97/24`
(`shell_two`, `shell_three`), as in the note's §6.
-/

@[expose] public section

namespace SLT.MiddlePositions

open MeasureTheory Set Metric SLT.PositionFour SLT.Pushforward
open scoped ENNReal NNReal Pointwise

/-! ### The two middle positions -/

/-- `l ↦ l³` is cubic for real scalars. -/
theorem twoCube_smul (c : ℝ) (g : Form × Form) : twoCube (c • g) = (c ^ 3) • twoCube g := by
  simp only [twoCube, Prod.smul_fst, Prod.smul_snd, Downstream.cube_smul, smul_add]

/-- The generators are linear in the four cubics jointly. -/
theorem generators_smul (c : ℝ) (p₁ q₁ p₂ q₂ : Cubic) :
    generators (c • p₁) (c • q₁) (c • p₂) (c • q₂) = c • generators p₁ q₁ p₂ q₂ := by
  funext i
  fin_cases i <;> simp [generators, Complex.real_smul] <;> ring

/-- `R₂ (c w) = c³ R₂ w`. -/
theorem R2_smul (c : ℝ) (w : Row2 × Row2) : R2 (c • w) = (c ^ 3) • R2 w := by
  simp only [R2, Prod.smul_fst, Prod.smul_snd, Downstream.cube_smul, twoCube_smul,
    generators_smul]

/-- `R₃ (c w) = c³ R₃ w`. -/
theorem R3_smul (c : ℝ) (w : Row3 × Row3) : R3 (c • w) = (c ^ 3) • R3 w := by
  simp only [R3, Prod.smul_fst, Prod.smul_snd, Downstream.cube_smul, twoCube_smul,
    generators_smul]

/-- `‖R₂ (c w)‖ = c³ ‖R₂ w‖` for `c > 0`. -/
theorem norm_R2_smul {c : ℝ} (hc : 0 < c) (w : Row2 × Row2) : ‖R2 (c • w)‖ = c ^ 3 * ‖R2 w‖ := by
  rw [R2_smul, norm_smul, Real.norm_of_nonneg (by positivity)]

/-- `‖R₃ (c w)‖ = c³ ‖R₃ w‖` for `c > 0`. -/
theorem norm_R3_smul {c : ℝ} (hc : 0 < c) (w : Row3 × Row3) : ‖R3 (c • w)‖ = c ^ 3 * ‖R3 w‖ := by
  rw [R3_smul, norm_smul, Real.norm_of_nonneg (by positivity)]

/-- `Row2 × Row2` has real dimension `24`. -/
theorem finrank_row2Pair : Module.finrank ℝ (Row2 × Row2) = 24 := by
  simp [Module.finrank_prod, Complex.finrank_real_complex]

/-- `Row3 × Row3` has real dimension `24`. -/
theorem finrank_row3Pair : Module.finrank ℝ (Row3 × Row3) = 24 := by
  simp [Module.finrank_prod, Complex.finrank_real_complex]

/-- The Borel structure on `Form`. -/
instance borelSpace_form : BorelSpace Form := Prod.borelSpace

/-- The Borel structure on `Form × Form`. -/
instance borelSpace_formPair : BorelSpace (Form × Form) := Prod.borelSpace

/-- The Borel structure on `Row2`. -/
instance borelSpace_row2 : BorelSpace Row2 := Prod.borelSpace

/-- The Borel structure on `Row3`. -/
instance borelSpace_row3 : BorelSpace Row3 := Prod.borelSpace

/-- The Borel structure on `Row2 × Row2`. -/
instance borelSpace_row2Pair : BorelSpace (Row2 × Row2) := Prod.borelSpace

/-- The Borel structure on `Row3 × Row3`. -/
instance borelSpace_row3Pair : BorelSpace (Row3 × Row3) := Prod.borelSpace

/-- Lebesgue measure on `Form` is an additive Haar measure. -/
instance isAddHaarMeasure_volume_form : (volume : Measure Form).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Lebesgue measure on `Row2 × Row2` is an additive Haar measure. -/
instance isAddHaarMeasure_volume_row2Pair : (volume : Measure (Row2 × Row2)).IsAddHaarMeasure := by
  have : (volume : Measure (Form × Form)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have : (volume : Measure Row2).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  exact Measure.prod.instIsAddHaarMeasure _ _

/-- Lebesgue measure on `Row3 × Row3` is an additive Haar measure. -/
instance isAddHaarMeasure_volume_row3Pair : (volume : Measure (Row3 × Row3)).IsAddHaarMeasure := by
  have : (volume : Measure (Form × Form)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have : (volume : Measure Row3).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  exact Measure.prod.instIsAddHaarMeasure _ _

/-- **The shell corollary at position two** (note §6): `SublevelTwo` gives
`∫_{1/2 ≤ ‖w‖ < 1} ‖R₂ w‖^{-2s} dw < ∞` for every `s < 97/24`. -/
theorem shell_two (h : SublevelTwo) {s : ℝ} (hs : s < 97 / 24) :
    ∫⁻ w in homShell (Row2 × Row2), ‖R2 w‖ₑ⁻¹ ^ (2 * s) < ∞ :=
  lintegral_homShell_lt_top_of_moment_24 volume continuous_R2 (fun _ hc w => norm_R2_smul hc w)
    finrank_row2Pair (β := 1 / 4) (by norm_num) (by linarith) h

/-- **The shell corollary at position three** (note §6): `SublevelThree` gives
`∫_{1/2 ≤ ‖w‖ < 1} ‖R₃ w‖^{-2s} dw < ∞` for every `s < 97/24`. -/
theorem shell_three (h : SublevelThree) {s : ℝ} (hs : s < 97 / 24) :
    ∫⁻ w in homShell (Row3 × Row3), ‖R3 w‖ₑ⁻¹ ^ (2 * s) < ∞ :=
  lintegral_homShell_lt_top_of_moment_24 volume continuous_R3 (fun _ hc w => norm_R3_smul hc w)
    finrank_row3Pair (β := 1 / 4) (by norm_num) (by linarith) h

end SLT.MiddlePositions
