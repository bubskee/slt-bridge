/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Template.Cone

/-!
# The elementary template, part 3: fibre theorems (brief 03, T1)

**Elementary template (upper half).** Let `G N x` be a fibre integral at a base point `x`. Suppose
that, uniformly in `x`, it satisfies the slice bound

`G N x ≤ min (T, A · N^{-λ} (log N)^{m-1} · w x)`.

* If `w` satisfies the logarithmic min-integral bound `MinLogBound` (weak-L¹ weights and critical
  weights on a pivot cone do), then `∫ G N ≤ C N^{-λ} (log N)^m`, with an explicit `C`
  (`lintegral_le_rate_of_minLogBound`, `laplaceUpper_of_minLogBound`). One extra log.
* If `w` is integrable, the rate is kept (`laplaceUpper_of_integrable`).

With a lower-bound core, this gives the learning pair (`hasLaplacePair_of_minLogBound`).
`lintegral_triangular` is the product step for a lower-triangular coupling: two blocks, where the
first block's bound is uniform in the second block's base point. It is used when the loss
splits into rows that are fibred one after another (Theorem M's F5).

The explicit constants depend only on `(A, B, D, λ)`. So the bounds are uniform over any family
of fibre problems that share these constants. Theorem M needs exactly this: the row bound is
applied at every frozen point of the other row.
-/

@[expose] public section

namespace SLT.Template

open MeasureTheory Set Real Filter
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- The explicit constant of the fibre theorem: `A (B + D (log⁺ A⁻¹ + λ))`. -/
noncomputable def fibreConst (A B D lam : ℝ) : ℝ :=
  A * (B + D * (Real.posLog A⁻¹ + lam))

/-- `log⁺ (1 / rate λ m N) ≤ λ log N` once `log N ≥ 1`. -/
theorem posLog_inv_rate_le {lam : ℝ} (hlam : 0 ≤ lam) (m : ℕ) {N : ℝ}
    (hN : Real.exp 1 ≤ N) : Real.posLog (rate lam m N)⁻¹ ≤ lam * Real.log N := by
  have hN1 : 1 < N := lt_of_lt_of_le (by linarith [Real.add_one_le_exp (1 : ℝ)]) hN
  have hN0 : 0 < N := one_pos.trans hN1
  have hl1 : 1 ≤ Real.log N := one_le_log_of_exp_le hN
  have hr : 0 < rate lam m N := rate_pos lam m hN1
  have hpow : 1 ≤ Real.log N ^ (m - 1) := one_le_pow₀ hl1
  have hNl : 1 ≤ N ^ lam := Real.one_le_rpow hN1.le hlam
  have hinv : (rate lam m N)⁻¹ ≤ N ^ lam := by
    unfold rate
    rw [mul_inv, Real.rpow_neg hN0.le, inv_inv]
    calc N ^ lam * (Real.log N ^ (m - 1))⁻¹ ≤ N ^ lam * 1 := by
          gcongr; exact inv_le_one_of_one_le₀ hpow
      _ = N ^ lam := mul_one _
  calc Real.posLog (rate lam m N)⁻¹ ≤ Real.posLog (N ^ lam) :=
        Real.posLog_le_posLog (by linarith [inv_pos.mpr hr]) hinv
    _ = Real.log (N ^ lam) := Real.posLog_eq_log (by rw [abs_of_pos (by positivity)]; exact hNl)
    _ = lam * Real.log N := Real.log_rpow hN0 lam

/-- **Fibre bound with a singular weight, explicit.** If `G x ≤ min (T, A · rate λ m N · w x)` for
`ρ`-a.e. `x`, `w` satisfies the logarithmic min-integral bound `MinLogBound ρ w T B D`, and
`N ≥ e`, then `∫ G ≤ fibreConst A B D λ · rate λ (m+1) N`. -/
theorem lintegral_le_rate_of_minLogBound {ρ : Measure X} {w : X → ℝ≥0∞} {A B D T lam : ℝ}
    {m : ℕ} (hML : MinLogBound ρ w T B D) (hA : 0 < A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hlam : 0 ≤ lam) (hm : 1 ≤ m) {N : ℝ} (hN : Real.exp 1 ≤ N) {G : X → ℝ≥0∞}
    (hG : ∀ᵐ x ∂ρ, G x ≤ min (ENNReal.ofReal T) (ENNReal.ofReal (A * rate lam m N) * w x)) :
    ∫⁻ x, G x ∂ρ ≤ ENNReal.ofReal (fibreConst A B D lam * rate lam (m + 1) N) := by
  have hN1 : 1 < N := lt_of_lt_of_le (by linarith [Real.add_one_le_exp (1 : ℝ)]) hN
  have hl1 : 1 ≤ Real.log N := one_le_log_of_exp_le hN
  have hr : 0 < rate lam m N := rate_pos lam m hN1
  set s := A * rate lam m N with hs
  have hs0 : 0 < s := mul_pos hA hr
  refine (lintegral_mono_ae hG).trans ((hML s hs0).trans (ENNReal.ofReal_le_ofReal ?_))
  have hlog : Real.posLog s⁻¹ ≤ (Real.posLog A⁻¹ + lam) * Real.log N := by
    have h1 : Real.posLog s⁻¹ ≤ Real.posLog A⁻¹ + lam * Real.log N := by
      rw [hs, mul_inv]
      exact Real.posLog_mul.trans (add_le_add le_rfl (posLog_inv_rate_le hlam m hN))
    have h3 : 0 ≤ Real.posLog A⁻¹ := Real.posLog_nonneg
    nlinarith
  have hrate : rate lam (m + 1) N = rate lam m N * Real.log N := by
    unfold rate
    rw [show m + 1 - 1 = (m - 1) + 1 by omega, pow_succ]; ring
  rw [hrate, fibreConst]
  have hB' : B ≤ B * Real.log N := le_mul_of_one_le_right hB hl1
  have hD' : D * Real.posLog s⁻¹ ≤ D * ((Real.posLog A⁻¹ + lam) * Real.log N) :=
    mul_le_mul_of_nonneg_left hlog hD
  calc s * (B + D * Real.posLog s⁻¹)
      ≤ s * (B * Real.log N + D * ((Real.posLog A⁻¹ + lam) * Real.log N)) := by gcongr
    _ = A * (B + D * (Real.posLog A⁻¹ + lam)) * (rate lam m N * Real.log N) := by
        rw [hs]; ring

/-- **Elementary template, upper half (singular weight): one extra log.** If, eventually in `N`,
the fibre integrals satisfy the slice bound `G N x ≤ min (T, A · rate λ m N · w x)` for `ρ`-a.e.
`x`, and `w` satisfies a logarithmic min-integral bound (for instance, `w` weak-L¹, or `w`
critically homogeneous on a pivot cone), then `N ↦ ∫ G N` has the upper rate `(λ, m+1)`. -/
theorem laplaceUpper_of_minLogBound {ρ : Measure X} {w : X → ℝ≥0∞} {A B D T lam : ℝ}
    {m : ℕ} (hML : MinLogBound ρ w T B D) (hA : 0 < A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hlam : 0 ≤ lam) (hm : 1 ≤ m) {G : ℝ → X → ℝ≥0∞}
    (hG : ∀ᶠ N in atTop, ∀ᵐ x ∂ρ,
      G N x ≤ min (ENNReal.ofReal T) (ENNReal.ofReal (A * rate lam m N) * w x)) :
    LaplaceUpper (fun N => ∫⁻ x, G N x ∂ρ) lam (m + 1) :=
  ⟨fibreConst A B D lam, by
    filter_upwards [hG, eventually_ge_atTop (Real.exp 1)] with N hGN hN
    exact lintegral_le_rate_of_minLogBound hML hA hB hD hlam hm hN hGN⟩

/-- **Elementary template, upper half (integrable weight): no extra log.** If, eventually in `N`,
`G N x ≤ A · rate λ m N · w x` for `ρ`-a.e. `x`, and `∫ w ≤ W`, then `N ↦ ∫ G N` has the upper rate
`(λ, m)`. -/
theorem laplaceUpper_of_integrable {ρ : Measure X} {w : X → ℝ≥0∞} (hw : AEMeasurable w ρ)
    {A W lam : ℝ} {m : ℕ} (hA : 0 ≤ A) (hW : ∫⁻ x, w x ∂ρ ≤ ENNReal.ofReal W)
    {G : ℝ → X → ℝ≥0∞}
    (hG : ∀ᶠ N in atTop, ∀ᵐ x ∂ρ, G N x ≤ ENNReal.ofReal (A * rate lam m N) * w x) :
    LaplaceUpper (fun N => ∫⁻ x, G N x ∂ρ) lam m :=
  ⟨A * W, by
    filter_upwards [hG, eventually_rate_nonneg lam m] with N hGN hr
    calc ∫⁻ x, G N x ∂ρ ≤ ∫⁻ x, ENNReal.ofReal (A * rate lam m N) * w x ∂ρ :=
          lintegral_mono_ae hGN
      _ = ENNReal.ofReal (A * rate lam m N) * ∫⁻ x, w x ∂ρ := lintegral_const_mul'' _ hw
      _ ≤ ENNReal.ofReal (A * rate lam m N) * ENNReal.ofReal W := by gcongr
      _ ≤ ENNReal.ofReal (A * W * rate lam m N) := by
          rcases le_or_gt W 0 with hW0 | hW0
          · rw [ENNReal.ofReal_of_nonpos hW0, mul_zero]; exact zero_le
          · rw [← ENNReal.ofReal_mul (mul_nonneg hA hr)]
            exact le_of_eq (congrArg _ (by ring))⟩

/-- **The elementary template (T1).** A lower-bound core `LaplaceLower F λ (m+1)`, a comparison
`F N ≤ ∫ G N` with fibre integrals `G`, a slice bound `G N x ≤ min (T, A · rate λ m N · w x)`
uniform in the base point, and a logarithmic min-integral bound on the weight together give the
learning pair `(λ, m+1)`. No resolution of singularities is used. -/
theorem hasLaplacePair_of_minLogBound {F : ℝ → ℝ≥0∞} {ρ : Measure X} {w : X → ℝ≥0∞}
    {A B D T lam : ℝ} {m : ℕ} (hML : MinLogBound ρ w T B D) (hA : 0 < A) (hB : 0 ≤ B)
    (hD : 0 ≤ D) (hlam : 0 ≤ lam) (hm : 1 ≤ m) {G : ℝ → X → ℝ≥0∞}
    (hlow : LaplaceLower F lam (m + 1)) (hcmp : ∀ᶠ N in atTop, F N ≤ ∫⁻ x, G N x ∂ρ)
    (hG : ∀ᶠ N in atTop, ∀ᵐ x ∂ρ,
      G N x ≤ min (ENNReal.ofReal T) (ENNReal.ofReal (A * rate lam m N) * w x)) :
    HasLaplacePair F lam (m + 1) :=
  ⟨by omega, hlow, (laplaceUpper_of_minLogBound hML hA hB hD hlam hm hG).mono hcmp⟩

/-! ### Two blocks with a lower-triangular coupling -/

variable {A₀ B₀ A₁ B₁ : Type*} [MeasurableSpace A₀] [MeasurableSpace B₀] [MeasurableSpace A₁]
  [MeasurableSpace B₁]

/-- **Triangular Fubini.** Take the integrand `F₀(a₀, b₀; a₁) · F₁(a₁, b₁; a₀)`. Block 0 sees
block 1 only through `a₁`, and block 1 sees block 0 only through `a₀`. Suppose block 0's
integral is at most `C₀` for a.e. frozen `a₁`, and block 1's fibre integral is at most `Ψ(a₁)`
uniformly in `a₀`, with `∫ Ψ ≤ C₁`. Then the whole integral is at most `C₀ C₁`. -/
theorem lintegral_triangular (α₀ : Measure A₀) (β₀ : Measure B₀) (α₁ : Measure A₁)
    (β₁ : Measure B₁) [SFinite α₀] [SFinite β₀] [SFinite α₁] [SFinite β₁]
    (F₀ : A₀ → B₀ → A₁ → ℝ≥0∞) (F₁ : A₁ → B₁ → A₀ → ℝ≥0∞)
    (hF₀ : Measurable fun p : A₀ × B₀ × A₁ => F₀ p.1 p.2.1 p.2.2)
    (hF₁ : Measurable fun p : A₁ × B₁ × A₀ => F₁ p.1 p.2.1 p.2.2) {C₀ C₁ : ℝ≥0∞} (hC₀ : C₀ ≠ ⊤)
    (Ψ : A₁ → ℝ≥0∞) (h₀ : ∀ᵐ a₁ ∂α₁, ∫⁻ a₀, ∫⁻ b₀, F₀ a₀ b₀ a₁ ∂β₀ ∂α₀ ≤ C₀)
    (h₁ : ∀ a₀ a₁, ∫⁻ b₁, F₁ a₁ b₁ a₀ ∂β₁ ≤ Ψ a₁) (hΨ : ∫⁻ a₁, Ψ a₁ ∂α₁ ≤ C₁) :
    ∫⁻ w, F₀ w.1.1 w.1.2 w.2.1 * F₁ w.2.1 w.2.2 w.1.1 ∂((α₀.prod β₀).prod (α₁.prod β₁)) ≤
      C₀ * C₁ := by
  have hW : Measurable fun w : (A₀ × B₀) × (A₁ × B₁) =>
      F₀ w.1.1 w.1.2 w.2.1 * F₁ w.2.1 w.2.2 w.1.1 :=
    (hF₀.comp (f := fun w : (A₀ × B₀) × (A₁ × B₁) => (w.1.1, w.1.2, w.2.1)) (by fun_prop)).mul
      (hF₁.comp (f := fun w : (A₀ × B₀) × (A₁ × B₁) => (w.2.1, w.2.2, w.1.1)) (by fun_prop))
  set G₀ : A₀ → A₁ → ℝ≥0∞ := fun a₀ a₁ => ∫⁻ b₀, F₀ a₀ b₀ a₁ ∂β₀ with hG₀
  have hG₀m : Measurable fun p : A₀ × A₁ => G₀ p.1 p.2 := by
    have : Measurable fun q : (A₀ × A₁) × B₀ => F₀ q.1.1 q.2 q.1.2 :=
      hF₀.comp (f := fun q : (A₀ × A₁) × B₀ => (q.1.1, q.2, q.1.2)) (by fun_prop)
    exact this.lintegral_prod_right'
  rw [lintegral_prod_symm _ hW.aemeasurable]
  have hin : ∀ r₁ : A₁ × B₁, ∫⁻ r₀, F₀ r₀.1 r₀.2 r₁.1 * F₁ r₁.1 r₁.2 r₀.1 ∂(α₀.prod β₀) =
      ∫⁻ a₀, G₀ a₀ r₁.1 * F₁ r₁.1 r₁.2 a₀ ∂α₀ := by
    intro r₁
    have hm : Measurable fun r₀ : A₀ × B₀ => F₀ r₀.1 r₀.2 r₁.1 * F₁ r₁.1 r₁.2 r₀.1 :=
      (hF₀.comp (f := fun r₀ : A₀ × B₀ => (r₀.1, r₀.2, r₁.1)) (by fun_prop)).mul
        (hF₁.comp (f := fun r₀ : A₀ × B₀ => (r₁.1, r₁.2, r₀.1)) (by fun_prop))
    rw [lintegral_prod _ hm.aemeasurable]
    refine lintegral_congr fun a₀ => ?_
    simp only [hG₀]
    exact lintegral_mul_const (μ := β₀) (f := fun b₀ => F₀ a₀ b₀ r₁.1) _
      (hF₀.comp (f := fun b₀ : B₀ => (a₀, b₀, r₁.1)) (by fun_prop))
  simp_rw [hin]
  have hJ : Measurable fun q : A₁ × B₁ × A₀ => G₀ q.2.2 q.1 * F₁ q.1 q.2.1 q.2.2 :=
    (hG₀m.comp (f := fun q : A₁ × B₁ × A₀ => (q.2.2, q.1)) (by fun_prop)).mul hF₁
  have hJ' : Measurable fun r₁ : A₁ × B₁ => ∫⁻ a₀, G₀ a₀ r₁.1 * F₁ r₁.1 r₁.2 a₀ ∂α₀ := by
    have : Measurable fun q : (A₁ × B₁) × A₀ => G₀ q.2 q.1.1 * F₁ q.1.1 q.1.2 q.2 :=
      (hG₀m.comp (f := fun q : (A₁ × B₁) × A₀ => (q.2, q.1.1)) (by fun_prop)).mul
        (hF₁.comp (f := fun q : (A₁ × B₁) × A₀ => (q.1.1, q.1.2, q.2)) (by fun_prop))
    exact this.lintegral_prod_right'
  rw [lintegral_prod _ hJ'.aemeasurable]
  calc ∫⁻ a₁, ∫⁻ b₁, ∫⁻ a₀, G₀ a₀ (a₁, b₁).1 * F₁ (a₁, b₁).1 (a₁, b₁).2 a₀ ∂α₀ ∂β₁ ∂α₁
      = ∫⁻ a₁, ∫⁻ a₀, G₀ a₀ a₁ * ∫⁻ b₁, F₁ a₁ b₁ a₀ ∂β₁ ∂α₀ ∂α₁ := by
        refine lintegral_congr fun a₁ => ?_
        have hsw : Measurable (Function.uncurry fun b₁ a₀ => G₀ a₀ a₁ * F₁ a₁ b₁ a₀) :=
          hJ.comp (f := fun p : B₁ × A₀ => (a₁, p.1, p.2)) (by fun_prop)
        rw [lintegral_lintegral_swap hsw.aemeasurable]
        refine lintegral_congr fun a₀ => ?_
        exact lintegral_const_mul _ (hF₁.comp (f := fun b₁ : B₁ => (a₁, b₁, a₀)) (by fun_prop))
    _ ≤ ∫⁻ a₁, ∫⁻ a₀, G₀ a₀ a₁ * Ψ a₁ ∂α₀ ∂α₁ :=
        lintegral_mono fun a₁ => lintegral_mono fun a₀ => by gcongr; exact h₁ a₀ a₁
    _ = ∫⁻ a₁, (∫⁻ a₀, G₀ a₀ a₁ ∂α₀) * Ψ a₁ ∂α₁ := by
        refine lintegral_congr fun a₁ => ?_
        exact lintegral_mul_const _ (hG₀m.comp (f := fun a₀ : A₀ => (a₀, a₁)) (by fun_prop))
    _ ≤ ∫⁻ a₁, C₀ * Ψ a₁ ∂α₁ := lintegral_mono_ae (h₀.mono fun a₁ h => by gcongr)
    _ = C₀ * ∫⁻ a₁, Ψ a₁ ∂α₁ := lintegral_const_mul' _ _ hC₀
    _ ≤ C₀ * C₁ := by gcongr

end SLT.Template
