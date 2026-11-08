/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT

/-!
# Zoo: one factored read/write block `c = u v³` (brief 03, T4)

Source: resnet-bridge `readwrite/R0_scalar.md` (Lemma R0.1 / Theorem R0.3, AI-reviewed, commit
`f9b4e78`; read only, not a dependency). One factored block replaces the raw scalar `w³` by
`c = u v³`. With target `c* = 0`, the local loss is `K(u, v) = (u v³)²`. R0.1 says that the crossing
stratum and the read-dead stratum behave identically, and differently from the write-dead stratum.
Here this is **Lean-certified** through the core's two-sided Newton theorem
(`SLT.Newton.newton_box_units`):

| stratum | point | local loss | `Γ` | pair |
|---|---|---|---|---|
| crossing | `(0, 0)` | `u² v⁶` | `{(2, 6)}` | `(1/6, 1)` (`oneBlock_crossing_pair`) |
| read-dead | `(u*, 0)`, `u* ≠ 0` | `≍ v⁶` | `{(0, 6)}` | `(1/6, 1)` (`oneBlock_readDead_pair`) |
| write-dead | `(0, v*)`, `v* ≠ 0` | `≍ u²` | `{(2, 0)}` | `(1/2, 1)` (`oneBlock_writeDead_pair`) |

The pairs are for the Lebesgue prior on a box around the point, in the original coordinates
(`Z_translate` moves the box to the origin). In read-dead the `u`-direction is flat: its exponent is
`0`.

The two-block identity group `(u₁ v₁³ + u₂ v₂³)²` is **not** covered. Its loss has a cancellation
hypersurface, so it is not comparable to a monomial sum. See `docs/status_log.md` (brief 03, T4).
-/

@[expose] public section

namespace SLT.Zoo.ReadWrite

open MeasureTheory Set SLT SLT.Newton SLT.NC
open scoped ENNReal

/-- The one-block local loss `K(u, v) = (u v³)²`, target `c* = 0`. -/
def oneBlockLoss (θ : Fin 2 → ℝ) : ℝ := (θ 0 * θ 1 ^ 3) ^ 2

/-- The one-block loss is measurable. -/
theorem measurable_oneBlockLoss : Measurable oneBlockLoss := by
  unfold oneBlockLoss; fun_prop

/-- **Moving the box to the origin**: the local free energy on the box around `p` is the free energy
of the shifted loss `y ↦ K (p + y)` on the box around `0`. -/
theorem Z_translate {d : ℕ} (p : Fin d → ℝ) (δ : ℝ) (K : (Fin d → ℝ) → ℝ) :
    Z (volume.restrict {θ | θ - p ∈ box δ}) K =
      Z (volume.restrict (box δ)) (fun y => K (p + y)) := by
  funext N
  simp only [Z]
  have e := (measurePreserving_add_left (volume : Measure (Fin d → ℝ)) p)
    |>.setLIntegral_comp_preimage_emb (MeasurableEquiv.addLeft p).measurableEmbedding
    (fun θ => ENNReal.ofReal (Real.exp (-(N * K θ)))) {θ | θ - p ∈ box δ}
  have hpre : (fun y => p + y) ⁻¹' {θ | θ - p ∈ box δ} = box δ := by
    ext y; simp
  rw [hpre] at e
  exact e.symm

/-! ### Newton data of the three strata -/

/-- A singleton set of optimal weights gives multiplicity one. -/
theorem newtonMult_eq_one_of_singleton {d : ℕ} {Γ : Finset (Fin d → ℝ)} {p : Fin d → ℝ}
    (h : optWeights Γ = {p}) : newtonMult Γ = 1 := by
  simp [newtonMult, h]

/-- Crossing: `t*({(2,6)}) = 6`. -/
theorem newtonDist_crossing : newtonDist ({![2, 6]} : Finset (Fin 2 → ℝ)) = 6 := by
  refine newtonDist_eq (u := ![0, 1]) ⟨fun i => by fin_cases i <;> norm_num,
    by simp [Fin.sum_univ_two], by simp [Fin.sum_univ_two]⟩ ?_
  rintro t' u' ⟨h0, h1, h2⟩
  have := h2 _ (Finset.mem_singleton_self _)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 this
  linarith [h0 0]

/-- Crossing: `O = {(0, 1)}`. -/
theorem optWeights_crossing : optWeights ({![2, 6]} : Finset (Fin 2 → ℝ)) = {![0, 1]} := by
  ext u
  simp only [optWeights, newtonDist_crossing, IsNewtonCert, Finset.mem_singleton, forall_eq,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨h0, h1, h2⟩
    have := h0 0
    funext i; fin_cases i <;> simp <;> nlinarith
  · rintro rfl
    exact ⟨fun i => by fin_cases i <;> norm_num, by simp, by simp⟩

/-- Read-dead: `t*({(0,6)}) = 6`. -/
theorem newtonDist_readDead : newtonDist ({![0, 6]} : Finset (Fin 2 → ℝ)) = 6 := by
  refine newtonDist_eq (u := ![0, 1]) ⟨fun i => by fin_cases i <;> norm_num,
    by simp [Fin.sum_univ_two], by simp [Fin.sum_univ_two]⟩ ?_
  rintro t' u' ⟨h0, h1, h2⟩
  have := h2 _ (Finset.mem_singleton_self _)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 this
  linarith [h0 0]

/-- Read-dead: `O = {(0, 1)}`. -/
theorem optWeights_readDead : optWeights ({![0, 6]} : Finset (Fin 2 → ℝ)) = {![0, 1]} := by
  ext u
  simp only [optWeights, newtonDist_readDead, IsNewtonCert, Finset.mem_singleton, forall_eq,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨h0, h1, h2⟩
    have := h0 0
    funext i; fin_cases i <;> simp <;> nlinarith
  · rintro rfl
    exact ⟨fun i => by fin_cases i <;> norm_num, by simp, by simp⟩

/-! ### The monomial sums -/

/-- Crossing: the monomial sum is the loss itself. -/
theorem monoSum_crossing (y : Fin 2 → ℝ) :
    monoSum ({![2, 6]} : Finset (Fin 2 → ℝ)) y = oneBlockLoss y := by
  simp only [monoSum, Finset.sum_singleton, monomial, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, oneBlockLoss]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, Real.rpow_natCast, mul_pow, ← pow_mul, pow_abs, pow_abs]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]

/-- Read-dead: the monomial sum is `v⁶`. -/
theorem monoSum_readDead (y : Fin 2 → ℝ) :
    monoSum ({![0, 6]} : Finset (Fin 2 → ℝ)) y = y 1 ^ 6 := by
  simp only [monoSum, Finset.sum_singleton, monomial, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.rpow_zero, one_mul]
  rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_abs,
    abs_of_nonneg (by positivity)]

/-- Write-dead: the monomial sum is `u²`. -/
theorem monoSum_writeDead (y : Fin 2 → ℝ) :
    monoSum ({![2, 0]} : Finset (Fin 2 → ℝ)) y = y 0 ^ 2 := by
  simp only [monoSum, Finset.sum_singleton, monomial, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.rpow_zero, mul_one]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]

/-! ### The three pairs -/

/-- The Lebesgue prior on the box, as the `withDensity 1` that `newton_box_units` takes. -/
theorem withDensity_one_box {d : ℕ} (δ : ℝ) :
    (volume.restrict (box (d := d) δ)).withDensity (fun _ => 1) = volume.restrict (box δ) :=
  withDensity_one

/-- **Crossing `(0,0)`: pair `(1/6, 1)`.** -/
theorem oneBlock_crossing_pair {δ : ℝ} (hδ : 0 < δ) :
    HasLaplacePair (Z (volume.restrict (box δ)) oneBlockLoss) (1 / 6) 1 := by
  have h := newton_box_units (d := 2) hδ (Γ := {![2, 6]})
    (by intro α hα i; rw [Finset.mem_singleton] at hα; subst hα; fin_cases i <;> norm_num)
    (by rw [newtonDist_crossing]; norm_num) measurable_oneBlockLoss (f := fun _ => 1)
    (a := 1) (b := 1) (c := 1) (C := 1) one_pos one_pos
    (fun y _ => by rw [monoSum_crossing, one_mul]) (fun y _ => by rw [monoSum_crossing, one_mul])
    (fun y _ => by simp) (fun y _ => by simp)
  rw [withDensity_one_box, newtonDist_crossing,
    newtonMult_eq_one_of_singleton optWeights_crossing] at h
  simpa using h

/-- **Read-dead `(u*, 0)`, `u* ≠ 0`: pair `(1/6, 1)`**, on any box of half-width `δ ≤ |u*|/2` around
the point. Near the point `K ≍ v⁶`, and the `u`-direction is flat. -/
theorem oneBlock_readDead_pair {us : ℝ} (hu : us ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hδu : δ ≤ |us| / 2) :
    HasLaplacePair (Z (volume.restrict {θ | θ - ![us, 0] ∈ box δ}) oneBlockLoss) (1 / 6) 1 := by
  rw [Z_translate]
  have hu0 : 0 < |us| := abs_pos.mpr hu
  have hfac : ∀ y ∈ box (d := 2) δ, (us / 2) ^ 2 ≤ (us + y 0) ^ 2 ∧
      (us + y 0) ^ 2 ≤ (3 * us / 2) ^ 2 := by
    intro y hy
    have hy0 : |y 0| ≤ δ := abs_le.mpr (hy 0 (mem_univ _))
    have h1 : |us| / 2 ≤ |us + y 0| := by
      have := abs_add_le (us + y 0) (-y 0)
      rw [add_neg_cancel_right, abs_neg] at this; linarith
    have h2 : |us + y 0| ≤ 3 * |us| / 2 := by
      have := abs_add_le us (y 0); linarith
    constructor
    · rw [← sq_abs (us + y 0), div_pow, ← sq_abs us]
      have := pow_le_pow_left₀ (by positivity) h1 2
      rw [div_pow] at this; exact this
    · rw [← sq_abs (us + y 0), show (3 * us / 2) ^ 2 = (3 * |us| / 2) ^ 2 by
        rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs]]
      exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hK : ∀ y : Fin 2 → ℝ, oneBlockLoss (![us, 0] + y) = (us + y 0) ^ 2 * y 1 ^ 6 := by
    intro y; simp only [oneBlockLoss, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_add]; ring
  have h := newton_box_units (d := 2) hδ (Γ := {![0, 6]})
    (K := fun y => oneBlockLoss (![us, 0] + y))
    (by intro α hα i; rw [Finset.mem_singleton] at hα; subst hα; fin_cases i <;> norm_num)
    (by rw [newtonDist_readDead]; norm_num)
    (measurable_oneBlockLoss.comp (measurable_const_add ![us, 0]))
    (f := fun _ => 1) (a := 1) (b := 1) (c := (us / 2) ^ 2) (C := (3 * us / 2) ^ 2) one_pos
    (by positivity)
    (fun y hy => by
      rw [monoSum_readDead, hK]; exact mul_le_mul_of_nonneg_right (hfac y hy).1 (by positivity))
    (fun y hy => by
      rw [monoSum_readDead, hK]; exact mul_le_mul_of_nonneg_right (hfac y hy).2 (by positivity))
    (fun y _ => by simp) (fun y _ => by simp)
  rw [withDensity_one_box, newtonDist_readDead,
    newtonMult_eq_one_of_singleton optWeights_readDead] at h
  simpa using h

/-- **Write-dead `(0, v*)`, `v* ≠ 0`: pair `(1/2, 1)`**, on any box of half-width `δ ≤ |v*|/2`
around the point. Near the point `K ≍ u²`. -/
theorem oneBlock_writeDead_pair {vs : ℝ} (hv : vs ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hδv : δ ≤ |vs| / 2) :
    HasLaplacePair (Z (volume.restrict {θ | θ - ![0, vs] ∈ box δ}) oneBlockLoss) (1 / 2) 1 := by
  rw [Z_translate]
  have hv0 : 0 < |vs| := abs_pos.mpr hv
  have hfac : ∀ y ∈ box (d := 2) δ, (vs / 2) ^ 6 ≤ (vs + y 1) ^ 6 ∧
      (vs + y 1) ^ 6 ≤ (3 * vs / 2) ^ 6 := by
    intro y hy
    have hy1 : |y 1| ≤ δ := abs_le.mpr (hy 1 (mem_univ _))
    have h1 : |vs| / 2 ≤ |vs + y 1| := by
      have := abs_add_le (vs + y 1) (-y 1)
      rw [add_neg_cancel_right, abs_neg] at this; linarith
    have h2 : |vs + y 1| ≤ 3 * |vs| / 2 := by
      have := abs_add_le vs (y 1); linarith
    have e6 : ∀ x : ℝ, x ^ 6 = |x| ^ 6 := fun x => by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, pow_mul, sq_abs]
    constructor
    · rw [e6 (vs + y 1), e6 (vs / 2), abs_div, abs_two]
      exact pow_le_pow_left₀ (by positivity) h1 6
    · rw [e6 (vs + y 1), e6 (3 * vs / 2), abs_div, abs_mul, abs_two,
        show |(3 : ℝ)| = 3 by norm_num]
      exact pow_le_pow_left₀ (abs_nonneg _) h2 6
  have hK : ∀ y : Fin 2 → ℝ, oneBlockLoss (![0, vs] + y) = (vs + y 1) ^ 6 * y 0 ^ 2 := by
    intro y; simp only [oneBlockLoss, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_add]; ring
  have h := newton_box_units (d := 2) hδ (Γ := {![2, 0]})
    (K := fun y => oneBlockLoss (![0, vs] + y))
    (by intro α hα i; rw [Finset.mem_singleton] at hα; subst hα; fin_cases i <;> norm_num)
    (by rw [newtonDist_sq_d2]; norm_num)
    (measurable_oneBlockLoss.comp (measurable_const_add ![0, vs]))
    (f := fun _ => 1) (a := 1) (b := 1) (c := (vs / 2) ^ 6) (C := (3 * vs / 2) ^ 6) one_pos
    (by positivity)
    (fun y hy => by
      rw [monoSum_writeDead, hK]; exact mul_le_mul_of_nonneg_right (hfac y hy).1 (by positivity))
    (fun y hy => by
      rw [monoSum_writeDead, hK]; exact mul_le_mul_of_nonneg_right (hfac y hy).2 (by positivity))
    (fun y _ => by simp) (fun y _ => by simp)
  rw [withDensity_one_box, newtonDist_sq_d2, newtonMult_sq_d2] at h
  simpa using h

/-- **R0.1's dichotomy**: crossing and read-dead have the same pair, and write-dead differs. -/
theorem crossing_readDead_ne_writeDead {us vs δ : ℝ} (hu : us ≠ 0) (hv : vs ≠ 0) (hδ : 0 < δ)
    (hδu : δ ≤ |us| / 2) (hδv : δ ≤ |vs| / 2) :
    HasLaplacePair (Z (volume.restrict (box δ)) oneBlockLoss) (1 / 6) 1 ∧
      HasLaplacePair (Z (volume.restrict {θ | θ - ![us, 0] ∈ box δ}) oneBlockLoss) (1 / 6) 1 ∧
      HasLaplacePair (Z (volume.restrict {θ | θ - ![0, vs] ∈ box δ}) oneBlockLoss) (1 / 2) 1 ∧
      (1 / 6 : ℝ) ≠ 1 / 2 :=
  ⟨oneBlock_crossing_pair hδ, oneBlock_readDead_pair hu hδ hδu, oneBlock_writeDead_pair hv hδ hδv,
    by norm_num⟩

end SLT.Zoo.ReadWrite
