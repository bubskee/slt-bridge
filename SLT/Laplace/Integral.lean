/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Laplace.Pair

/-!
# The Laplace integral `Z(N) = ∫ e^{-N K} dν`

`Z ν K N : ℝ≥0∞` is a lower Lebesgue integral, so it needs no integrability side conditions. The
prior and any cutoff are part of the measure `ν`, e.g. `(volume.restrict W).withDensity φ`.
`V ν K t = ν {K ≤ t}` is the sublevel volume.

* comparable losses (`c K ≤ K' ≤ C K` a.e.) have the same pair;
* comparable priors (`a ν ≤ ν' ≤ b ν`, or densities bounded between positive constants) have the
  same pair;
* losses in disjoint variable blocks: pairs combine as `(λ₁+λ₂, m₁+m₂-1)`;
* `Z(N) ≥ e^{-1} V(1/N)`;
* the Bochner form `∫ e^{-N K} dν` for finite `ν` and `K ≥ 0`, giving `HasLaplaceOrder` (the scalar
  library's predicate) and `IsTheta` (grammar's `LaplaceTheta`).
-/

@[expose] public section

namespace SLT

open MeasureTheory Filter Asymptotics Real Set
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The Laplace integral `Z(N) = ∫ e^{-N K} dν`. -/
noncomputable def Z (ν : Measure α) (K : α → ℝ) (N : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (-(N * K x))) ∂ν

/-- The sublevel volume `V(t) = ν {K ≤ t}`. -/
def V (ν : Measure α) (K : α → ℝ) (t : ℝ) : ℝ≥0∞ := ν {x | K x ≤ t}

variable {ν ν' : Measure α} {K K' : α → ℝ} {N lam : ℝ} {m : ℕ}

/-! ### Losses -/

/-- Scaling the loss is scaling `N`: `Z ν (c K) N = Z ν K (c N)`. -/
theorem Z_mul_loss (c : ℝ) : Z ν (fun x => c * K x) N = Z ν K (c * N) := by
  unfold Z; congr 1; funext x; ring_nf

/-- `Z` is antitone in the loss (for `N ≥ 0`). -/
theorem Z_anti_loss (h : ∀ᵐ x ∂ν, K x ≤ K' x) (hN : 0 ≤ N) : Z ν K' N ≤ Z ν K N :=
  lintegral_mono_ae <| h.mono fun x hx => ENNReal.ofReal_le_ofReal <| Real.exp_le_exp.mpr <| by
    have := mul_le_mul_of_nonneg_left hx hN; linarith

/-- If `c K ≤ K'` a.e., then `Z ν K' N ≤ Z ν K (c N)` for `N ≥ 0`. -/
theorem Z_le_of_mul_le {c : ℝ} (hlo : ∀ᵐ x ∂ν, c * K x ≤ K' x) (hN : 0 ≤ N) :
    Z ν K' N ≤ Z ν K (c * N) := by
  rw [← Z_mul_loss]; exact Z_anti_loss hlo hN

/-- If `K' ≤ C K` a.e., then `Z ν K (C N) ≤ Z ν K' N` for `N ≥ 0`. -/
theorem Z_ge_of_le_mul {C : ℝ} (hhi : ∀ᵐ x ∂ν, K' x ≤ C * K x) (hN : 0 ≤ N) :
    Z ν K (C * N) ≤ Z ν K' N := by
  rw [← Z_mul_loss]; exact Z_anti_loss hhi hN

/-- If `K' ≤ C K` a.e. (`C > 0`), a lower bound for `Z ν K` gives one for `Z ν K'`. -/
theorem LaplaceLower.of_le_mul {C : ℝ} (hC : 0 < C) (hhi : ∀ᵐ x ∂ν, K' x ≤ C * K x)
    (h : LaplaceLower (Z ν K) lam m) : LaplaceLower (Z ν K') lam m :=
  (h.comp_mul hC).mono <| (eventually_ge_atTop 0).mono fun _ hN => Z_ge_of_le_mul hhi hN

/-- If `c K ≤ K'` a.e. (`c > 0`), an upper bound for `Z ν K` gives one for `Z ν K'`. -/
theorem LaplaceUpper.of_mul_le {c : ℝ} (hc : 0 < c) (hlo : ∀ᵐ x ∂ν, c * K x ≤ K' x)
    (h : LaplaceUpper (Z ν K) lam m) : LaplaceUpper (Z ν K') lam m :=
  (h.comp_mul hc).mono <| (eventually_ge_atTop 0).mono fun _ hN => Z_le_of_mul_le hlo hN

/-- (M1) **Comparable losses have the same pair.** -/
theorem HasLaplacePair.of_comparable {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hlo : ∀ᵐ x ∂ν, c * K x ≤ K' x) (hhi : ∀ᵐ x ∂ν, K' x ≤ C * K x)
    (h : HasLaplacePair (Z ν K) lam m) : HasLaplacePair (Z ν K') lam m :=
  ⟨h.1, h.2.1.of_le_mul hC hhi, h.2.2.of_mul_le hc hlo⟩

/-! ### Priors -/

/-- `Z` is linear in scalar multiples of the measure. -/
theorem Z_smul_measure (a : ℝ≥0∞) : Z (a • ν) K N = a * Z ν K N := by
  rw [Z, Z, lintegral_smul_measure, smul_eq_mul]

/-- `Z` is monotone in the measure. -/
theorem Z_mono_measure (h : ν ≤ ν') : Z ν K N ≤ Z ν' K N := lintegral_mono' h le_rfl

/-- (M1) **Comparable priors have the same pair**: `a ν ≤ ν' ≤ b ν` with `0 < a`, `b < ∞`. -/
theorem HasLaplacePair.of_prior {a b : ℝ≥0∞} (ha : a ≠ 0) (ha' : a ≠ ⊤) (hb : b ≠ ⊤)
    (hlo : a • ν ≤ ν') (hhi : ν' ≤ b • ν) (h : HasLaplacePair (Z ν K) lam m) :
    HasLaplacePair (Z ν' K) lam m :=
  ⟨h.1, (h.2.1.const_mul ha ha').mono (Eventually.of_forall fun _ => by
      rw [← Z_smul_measure]; exact Z_mono_measure hlo),
    (h.2.2.const_mul hb).mono (Eventually.of_forall fun _ => by
      rw [← Z_smul_measure]; exact Z_mono_measure hhi)⟩

/-- (M1) **Prior densities bounded between positive constants** do not change the pair. -/
theorem HasLaplacePair.withDensity {f : α → ℝ≥0∞} {a b : ℝ≥0∞} (ha : a ≠ 0) (ha' : a ≠ ⊤)
    (hb : b ≠ ⊤) (hlo : ∀ᵐ x ∂ν, a ≤ f x) (hhi : ∀ᵐ x ∂ν, f x ≤ b)
    (h : HasLaplacePair (Z ν K) lam m) : HasLaplacePair (Z (ν.withDensity f) K) lam m :=
  h.of_prior ha ha' hb (by rw [← withDensity_const]; exact withDensity_mono hlo)
    (by rw [← withDensity_const]; exact withDensity_mono hhi)

/-! ### Products: losses in disjoint variable blocks -/

/-- `Z_{K₁ ⊕ K₂} = Z_{K₁} · Z_{K₂}` on a product measure (Tonelli). -/
theorem Z_prod {ν₁ : Measure α} {ν₂ : Measure β} [SFinite ν₂] {K₁ : α → ℝ} {K₂ : β → ℝ}
    (h₁ : Measurable K₁) (h₂ : Measurable K₂) (N : ℝ) :
    Z (ν₁.prod ν₂) (fun p => K₁ p.1 + K₂ p.2) N = Z ν₁ K₁ N * Z ν₂ K₂ N := by
  unfold Z
  rw [← lintegral_prod_mul (by fun_prop) (by fun_prop)]
  congr 1; funext p
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; congr 2; ring

/-- (M1) **Pairs add over disjoint blocks**: `(λ₁, m₁)` and `(λ₂, m₂)` give `(λ₁+λ₂, m₁+m₂-1)`. -/
theorem HasLaplacePair.prod {ν₁ : Measure α} {ν₂ : Measure β} [SFinite ν₂]
    {K₁ : α → ℝ} {K₂ : β → ℝ} (h₁ : Measurable K₁) (h₂ : Measurable K₂) {l₁ l₂ : ℝ} {m₁ m₂ : ℕ}
    (H₁ : HasLaplacePair (Z ν₁ K₁) l₁ m₁) (H₂ : HasLaplacePair (Z ν₂ K₂) l₂ m₂) :
    HasLaplacePair (Z (ν₁.prod ν₂) (fun p => K₁ p.1 + K₂ p.2)) (l₁ + l₂) (m₁ + m₂ - 1) :=
  (H₁.mul H₂).congr (Eventually.of_forall fun N => (Z_prod h₁ h₂ N).symm)

/-! ### Volume, lower direction -/

/-- `Z(N) ≥ e^{-1} V(1/N)` for `N > 0`. -/
theorem Z_ge_V (hK : Measurable K) (hN : 0 < N) :
    ENNReal.ofReal (Real.exp (-1)) * V ν K N⁻¹ ≤ Z ν K N := by
  have hmeas : Measurable fun x => ENNReal.ofReal (Real.exp (-(N * K x))) := by fun_prop
  refine le_trans ?_ (mul_meas_ge_le_lintegral₀ hmeas.aemeasurable
    (ENNReal.ofReal (Real.exp (-1))))
  unfold V
  gcongr with x
  intro hx
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have : N * K x ≤ 1 := by rw [← le_div_iff₀' hN, one_div]; exact hx
  linarith

/-- `V(1/N) ≤ e · Z(N)` for `N > 0` (Chebyshev). -/
theorem V_le_Z (hK : Measurable K) (hN : 0 < N) :
    V ν K N⁻¹ ≤ ENNReal.ofReal (Real.exp 1) * Z ν K N := by
  have e : V ν K N⁻¹ =
      ENNReal.ofReal (Real.exp 1) * (ENNReal.ofReal (Real.exp (-1)) * V ν K N⁻¹) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; simp
  rw [e]; gcongr; exact Z_ge_V hK hN

/-! ### Pieces for gluing: covers and exponentially small regions -/

/-- (M1) **Cover bound**: the integral over a finite union is at most the sum over the pieces
(overlaps allowed, since the integrand is nonnegative). -/
theorem Z_restrict_iUnion_le {ι : Type*} [Fintype ι] (A : ι → Set α) (N : ℝ) :
    Z (ν.restrict (⋃ i, A i)) K N ≤ ∑ i, Z (ν.restrict (A i)) K N := by
  calc Z (ν.restrict (⋃ i, A i)) K N ≤ Z (Measure.sum fun i => ν.restrict (A i)) K N :=
        Z_mono_measure Measure.restrict_iUnion_le
    _ = _ := by rw [Z, lintegral_sum_measure, tsum_fintype]; rfl

/-- Restricting the measure decreases `Z`. -/
theorem Z_restrict_le (A : Set α) (N : ℝ) : Z (ν.restrict A) K N ≤ Z ν K N :=
  Z_mono_measure Measure.restrict_le_self

/-- Where `K ≥ a`, `Z(N) ≤ ν(univ) e^{-a N}`. -/
theorem Z_le_of_loss_ge {a : ℝ} (hK : ∀ᵐ x ∂ν, a ≤ K x) (hN : 0 ≤ N) :
    Z ν K N ≤ ν univ * ENNReal.ofReal (Real.exp (-a * N)) := by
  calc Z ν K N ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (-a * N)) ∂ν :=
        lintegral_mono_ae (hK.mono fun x hx => ENNReal.ofReal_le_ofReal
          (Real.exp_le_exp.mpr (by nlinarith)))
    _ = _ := by rw [lintegral_const, mul_comm]

/-- (M1) **A region where `K` is bounded below contributes below every rate.** -/
theorem laplaceUpper_of_loss_ge [IsFiniteMeasure ν] {a : ℝ} (ha : 0 < a)
    (hK : ∀ᵐ x ∂ν, a ≤ K x) (lam : ℝ) (m : ℕ) : LaplaceUpper (Z ν K) lam m := by
  refine laplaceUpper_of_exp (C := (ν univ).toReal) ha ?_ lam m
  filter_upwards [eventually_ge_atTop 0] with N hN
  refine (Z_le_of_loss_ge hK hN).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_toReal (measure_ne_top ν univ), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (measure_ne_top ν univ)]

/-! ### Bochner form -/

/-- For integrable `e^{-N K}`, `Z` is the `ofReal` of the Bochner integral. -/
theorem Z_eq_ofReal_integral (hint : Integrable (fun x => Real.exp (-(N * K x))) ν) :
    Z ν K N = ENNReal.ofReal (∫ x, Real.exp (-(N * K x)) ∂ν) :=
  (ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)).symm

/-- For finite `ν`, nonnegative `K` and `N ≥ 0`, `e^{-N K}` is integrable. -/
theorem integrable_exp_neg_mul [IsFiniteMeasure ν] (hK : Measurable K) (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x)
    (hN : 0 ≤ N) : Integrable (fun x => Real.exp (-(N * K x))) ν := by
  refine Integrable.of_bound (by fun_prop : Measurable _).aestronglyMeasurable 1 ?_
  filter_upwards [hK0] with x hx
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
  have := mul_nonneg hN hx; linarith

/-- For finite `ν` and `K ≥ 0` a.e., `Z` eventually agrees with the Bochner integral, written as
`∫ e^{-N K}` with `-N * K x` (the form used by the scalar library and grammar). -/
theorem Z_eventuallyEq_integral [IsFiniteMeasure ν] (hK : Measurable K) (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) :
    Z ν K =ᶠ[atTop] fun N => ENNReal.ofReal (∫ x, Real.exp (-N * K x) ∂ν) := by
  filter_upwards [eventually_ge_atTop 0] with N hN
  rw [Z_eq_ofReal_integral (integrable_exp_neg_mul hK hK0 hN)]
  simp only [neg_mul]

/-- (M1) **Bridge to `ResidualSLT.HasLaplaceOrder`** for the Bochner Laplace integral. -/
theorem hasLaplacePair_Z_iff_hasLaplaceOrder [IsFiniteMeasure ν] (hK : Measurable K)
    (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) :
    HasLaplacePair (Z ν K) lam m ↔
      HasLaplaceOrder lam m (fun N => ∫ x, Real.exp (-N * K x) ∂ν) := by
  rw [← hasLaplacePair_ofReal_iff]
  have e := Z_eventuallyEq_integral hK hK0
  exact ⟨fun h => h.congr e, fun h => h.congr e.symm⟩

/-- (M1) **From the scalar library's `HasLaplaceOrder` to `HasLaplacePair (Z ν K)`, with no side
conditions.** The lower bound makes the Bochner integral positive for large `N`, so
`e^{-N K}` is integrable there and `Z ν K N` is its `ofReal`. -/
theorem hasLaplacePair_Z_of_hasLaplaceOrder
    (h : HasLaplaceOrder lam m (fun N => ∫ x, Real.exp (-N * K x) ∂ν)) :
    HasLaplacePair (Z ν K) lam m := by
  have hp := hasLaplacePair_ofReal_iff.mpr h
  refine hp.congr ?_
  obtain ⟨-, c, C, N₀, hc, -, hN₀, hb⟩ := h
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hpos : 0 < ∫ x, Real.exp (-N * K x) ∂ν :=
    lt_of_lt_of_le (mul_pos hc (rate_pos lam m (hN₀.trans_le hN))) (hb N hN).1
  have hint : Integrable (fun x => Real.exp (-(N * K x))) ν := by
    by_contra hni
    have : ¬ Integrable (fun x => Real.exp (-N * K x)) ν := by simpa only [neg_mul] using hni
    rw [integral_undef this] at hpos
    exact lt_irrefl _ hpos
  rw [Z_eq_ofReal_integral hint]
  simp only [neg_mul]

/-- (M1) **Bridge to grammar's `LaplaceTheta`**: `(N ↦ ∫ e^{-N K} dν) =Θ[atTop] rate λ m`. -/
theorem hasLaplacePair_Z_iff_isTheta [IsFiniteMeasure ν] (hK : Measurable K)
    (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) (hm : 1 ≤ m) :
    HasLaplacePair (Z ν K) lam m ↔
      (fun N => ∫ x, Real.exp (-N * K x) ∂ν) =Θ[atTop] rate lam m := by
  rw [← hasLaplacePair_ofReal_iff_isTheta (Eventually.of_forall fun _ =>
    integral_nonneg fun _ => (Real.exp_pos _).le) hm]
  have e := Z_eventuallyEq_integral hK hK0
  exact ⟨fun h => h.congr e, fun h => h.congr e.symm⟩

end SLT
