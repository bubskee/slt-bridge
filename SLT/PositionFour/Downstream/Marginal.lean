/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Defs
public import SLT.PositionFour.Upstream.Algebra
public import SLT.Pushforward.QuadraticDisc

/-!
# The transverse marginal and its pointwise bounds

Section 2 of `complex_position_four.tex`. Write `P = (λ, y)` with `λ = (P₀, P₁)` and
`y = (P₂, P₃)`. The **transverse marginal** is
`m_β(λ) = ∫_{|P₂|, |P₃| < 1} densityBound β (λ, y) dy`.

As a quadratic in `P₃`,
`𝔇 = P₀² P₃² + (4P₁³ - 6P₀P₁P₂) P₃ + (4P₀P₂³ - 3P₁²P₂²)`, with `P₃`-discriminant
`16 (P₁² - P₀P₂)³` (`disc_toCubic`, `discr_disc`).

The note proves its bounds in spherical coordinates `λ = R λ̂`, `ε = 1/R`, and for small `ε`. Here
they are proved **directly in `λ`, for every `‖λ‖ ≥ 1`**, with no chart rescaling:

* `transverseMarginal_le_central` (`P₀ ≠ 0`): the two-root estimate, the note's (central);
* `transverseMarginal_le_outer` (`|P₁| ≥ 1`, `6|P₀| ≤ |P₁|²`, `8|P₀|² ≤ |P₁|³`): the
  one-dominant-root estimate, the note's (outer), which also covers the directions near `P₀ = 0`.

The note's logarithm `1 + log(1/ε)` is replaced by `|P₀|^{η/2}` for an arbitrary `η > 0`.
-/

@[expose] public section

namespace SLT.PositionFour.Downstream

open MeasureTheory Set Real Metric SLT.Pushforward
open scoped ENNReal NNReal

/-! ### Coordinates and algebra -/

/-- The cubic with moment coordinates `(P₀, P₁, P₂, P₃) = (λ₁, λ₂, y₁, y₂)`. -/
def toCubic (lam y : ℂ × ℂ) : Cubic := ![lam.1, lam.2, y.1, y.2]

/-- `𝔇` in the coordinates `(λ, y)`, as a quadratic in `P₃ = y₂`. -/
theorem disc_toCubic (lam y : ℂ × ℂ) :
    disc (toCubic lam y) = lam.1 ^ 2 * y.2 ^ 2 + (4 * lam.2 ^ 3 - 6 * lam.1 * lam.2 * y.1) * y.2 +
      (4 * lam.1 * y.1 ^ 3 - 3 * lam.2 ^ 2 * y.1 ^ 2) := by
  simp [disc, toCubic]; ring

/-- The hint's form of the root structure:
`4 P₀² 𝔇 = (2P₀²P₃ + 4P₁³ - 6P₀P₁P₂)² - 16(P₁² - P₀P₂)³`. -/
theorem four_mul_sq_mul_disc (P : Cubic) :
    4 * P 0 ^ 2 * disc P = (2 * P 0 ^ 2 * P 3 + 4 * P 1 ^ 3 - 6 * P 0 * P 1 * P 2) ^ 2 -
      16 * (P 1 ^ 2 - P 0 * P 2) ^ 3 := by
  simp only [disc]; ring

/-- `𝔇` is continuous. -/
theorem continuous_disc : Continuous disc := by unfold disc; fun_prop

/-- The Hessian covariant is continuous. -/
theorem continuous_hess : Continuous hess := by unfold hess; fun_prop

/-- The bounding density is measurable. -/
theorem measurable_densityBound (β : ℝ) : Measurable (densityBound β) := by
  have h1 := continuous_disc.measurable
  have h2 := continuous_hess.measurable
  unfold densityBound
  fun_prop

/-- On the box, `‖P‖ ≤ ‖λ‖` once `‖λ‖ ≥ 1`. -/
theorem norm_toCubic_le {lam y : ℂ × ℂ} (hlam : 1 ≤ ‖lam‖) (hy : ‖y‖ < 1) :
    ‖toCubic lam y‖ ≤ ‖lam‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  have h1 := norm_fst_le lam; have h2 := norm_snd_le lam
  have h3 := norm_fst_le y; have h4 := norm_snd_le y
  fin_cases i <;> simp [toCubic] <;> linarith

/-- On the box, `‖H(P)‖ ≤ |P₁² - P₀P₂| + (|P₀| + |P₁| + 1)`. -/
theorem norm_hess_toCubic_le (lam : ℂ × ℂ) {y : ℂ × ℂ} (hy : ‖y‖ ≤ 1) :
    ‖hess (toCubic lam y)‖ ≤ ‖lam.2 ^ 2 - lam.1 * y.1‖ + (‖lam.1‖ + ‖lam.2‖ + 1) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  have h3 : ‖y.1‖ ≤ 1 := (norm_fst_le y).trans hy
  have h4 : ‖y.2‖ ≤ 1 := (norm_snd_le y).trans hy
  have n0 := norm_nonneg lam.1; have n1 := norm_nonneg lam.2
  have n2 := norm_nonneg y.1; have n3 := norm_nonneg y.2
  have nd := norm_nonneg (lam.2 ^ 2 - lam.1 * y.1)
  have e : hess (toCubic lam y) =
      ![lam.1 * y.1 - lam.2 ^ 2, lam.1 * y.2 - lam.2 * y.1, lam.2 * y.2 - y.1 ^ 2] := rfl
  rw [e]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · rw [show lam.1 * y.1 - lam.2 ^ 2 = -(lam.2 ^ 2 - lam.1 * y.1) by ring, norm_neg]
    linarith
  · calc ‖lam.1 * y.2 - lam.2 * y.1‖ ≤ ‖lam.1‖ * ‖y.2‖ + ‖lam.2‖ * ‖y.1‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ ‖lam.1‖ * 1 + ‖lam.2‖ * 1 := by gcongr
      _ ≤ _ := by linarith
  · calc ‖lam.2 * y.2 - y.1 ^ 2‖ ≤ ‖lam.2‖ * ‖y.2‖ + ‖y.1‖ ^ 2 := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_pow]
      _ ≤ ‖lam.2‖ * 1 + 1 ^ 2 := by gcongr
      _ ≤ _ := by linarith

/-! ### The marginal -/

/-- The transverse marginal `m_β(λ) = ∫_{|P₂|, |P₃| < 1} densityBound β (λ, y) dy` (sup norm on
`y = (P₂, P₃)`). -/
noncomputable def transverseMarginal (β : ℝ) (lam : ℂ × ℂ) : ℝ≥0∞ :=
  ∫⁻ y in ball (0 : ℂ × ℂ) 1, densityBound β (toCubic lam y)

/-- The bounding density on the box, with `‖P‖ ≤ ‖λ‖` and `‖H‖ ≤ |P₁² - P₀P₂| + N`. -/
theorem densityBound_toCubic_le {β : ℝ} (hβ : 0 ≤ β) {lam y : ℂ × ℂ} (hlam : 1 ≤ ‖lam‖)
    (hy : ‖y‖ < 1) :
    densityBound β (toCubic lam y) ≤
      ENNReal.ofReal (‖lam‖ ^ (β / 3)) * ‖disc (toCubic lam y)‖ₑ⁻¹ ^ (1 + 0 : ℝ) +
      ENNReal.ofReal ((‖lam.2 ^ 2 - lam.1 * y.1‖ + (‖lam.1‖ + ‖lam.2‖ + 1)) ^ (β / 2)) *
        ‖disc (toCubic lam y)‖ₑ⁻¹ ^ (1 + β / 6) := by
  unfold densityBound
  rw [add_zero, ENNReal.rpow_one, ← enorm_eq_nnnorm]
  gcongr
  · exact norm_toCubic_le hlam hy
  · exact norm_hess_toCubic_le lam hy.le

/-- Tonelli on the box `ball 0 1 ⊆ ℂ × ℂ`. -/
theorem setLIntegral_ball_prod {G : ℂ × ℂ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ y in ball (0 : ℂ × ℂ) 1, G y = ∫⁻ a in ball (0 : ℂ) 1, ∫⁻ b in ball (0 : ℂ) 1, G (a, b) := by
  rw [show (0 : ℂ × ℂ) = ((0 : ℂ), (0 : ℂ)) from rfl, ← ball_prod_same, Measure.volume_eq_prod,
    ← Measure.prod_restrict, lintegral_prod _ hG.aemeasurable]

/-- The `P₂`-integral of `|P₁² - P₀ P₂|^{-s}` over the unit disc, for `P₀ ≠ 0`, `0 ≤ s < 2`. -/
theorem lintegral_ball_inv_delta_le {P₀ : ℂ} (hP₀ : P₀ ≠ 0) (P₁ : ℂ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < 2) :
    ∫⁻ P₂ in ball (0 : ℂ) 1, ‖P₁ ^ 2 - P₀ * P₂‖ₑ⁻¹ ^ s ≤
      ENNReal.ofReal (‖P₀‖ ^ (-s) * (2 * π / (2 - s) + π)) := by
  have e : ∀ P₂ : ℂ, P₁ ^ 2 - P₀ * P₂ = (-P₀) * (P₂ - P₁ ^ 2 / P₀) := fun P₂ => by
    field_simp; ring
  simp_rw [e, enorm_mul_inv_rpow (neg_ne_zero.mpr hP₀) _ hs0, norm_neg]
  rw [lintegral_const_mul _ (by fun_prop)]
  calc _ ≤ ENNReal.ofReal (‖P₀‖ ^ (-s)) * ENNReal.ofReal ((2 * π / (2 - s) + π) * 1 ^ (2 - s)) := by
        gcongr; exact lintegral_ball_sub_inv_rpow_le _ hs0 hs one_pos
    _ = _ := by rw [Real.one_rpow, mul_one, ← ENNReal.ofReal_mul (by positivity)]

/-- **The `P₃`-integral, two roots** (`P₀ ≠ 0`): with `b = 2a + η`,
`∫_{|P₃| < 1} |𝔇|^{-1-a} ≤ c |P₀|^{2(b-1-a)} |P₁² - P₀P₂|^{-3b/2}`. -/
theorem lintegral_ball_inv_disc_le {lam : ℂ × ℂ} (hP₀ : lam.1 ≠ 0) (P₂ : ℂ) {a η : ℝ}
    (ha : 0 ≤ a) (hη : 0 < η) (haη : a + η ≤ 1) :
    ∫⁻ P₃ in ball (0 : ℂ) 1, ‖disc (toCubic lam (P₂, P₃))‖ₑ⁻¹ ^ (1 + a) ≤
      ENNReal.ofReal (2 ^ (2 * a + η + 1) * (2 * π / η + π) * 16 ^ (-((2 * a + η) / 2)) *
        ‖lam.1‖ ^ (2 * (2 * a + η - 1 - a))) *
        ‖lam.2 ^ 2 - lam.1 * P₂‖ₑ⁻¹ ^ (3 * ((2 * a + η) / 2)) := by
  simp_rw [disc_toCubic]
  refine (lintegral_ball_inv_quadratic_le (pow_ne_zero 2 hP₀) ha hη haη one_pos).trans
    (le_of_eq ?_)
  rw [discr_disc, enorm_mul_inv_rpow (by norm_num) _ (by positivity), enorm_pow_inv_rpow,
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [norm_pow, Real.one_rpow, mul_one, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  norm_num
  ring

private lemma rpow_mul_rpow_of_add {x : ℝ} (hx : 0 < x) {a b c : ℝ} (h : a + b = c) :
    x ^ a * x ^ b = x ^ c := by rw [← Real.rpow_add hx, h]

/-- **The central bound** (`P₀ ≠ 0`, every `‖λ‖ ≥ 1`): with `N = |P₀| + |P₁| + 1`,
`m_β(λ) ≤ K (‖λ‖^{β/3} |P₀|^{-2+η/2} + |P₀|^{-2+β/3+η/2} + N^{β/2} |P₀|^{-2-β/6+η/2})`.
No smallness of `1/‖λ‖` is assumed: this settles the note's range of `ε` of order one. -/
theorem transverseMarginal_le_central {β η : ℝ} (hβ0 : 0 ≤ β) (hβ2 : β < 2) (hη : 0 < η)
    (hη1 : η ≤ 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lam : ℂ × ℂ, lam.1 ≠ 0 → 1 ≤ ‖lam‖ →
      transverseMarginal β lam ≤ ENNReal.ofReal (K * (‖lam‖ ^ (β / 3) * ‖lam.1‖ ^ (-2 + η / 2) +
        ‖lam.1‖ ^ (-2 + β / 3 + η / 2) +
        (‖lam.1‖ + ‖lam.2‖ + 1) ^ (β / 2) * ‖lam.1‖ ^ (-2 - β / 6 + η / 2))) := by
  set a := β / 6 with ha_def
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a < 1 / 3 := by rw [ha_def]; linarith
  -- the constants
  set c : ℝ → ℝ := fun a => 2 ^ (2 * a + η + 1) * (2 * π / η + π) * 16 ^ (-((2 * a + η) / 2))
    with hc
  set k : ℝ → ℝ := fun s => 2 * π / (2 - s) + π with hk
  set s₀ := 3 * ((2 * 0 + η) / 2) with hs₀
  set s₁ := 3 * ((2 * a + η) / 2) with hs₁
  have hs₀' : s₀ = 3 * η / 2 := by rw [hs₀]; ring
  have hs₁' : s₁ = β / 2 + 3 * η / 2 := by rw [hs₁, ha_def]; ring
  have hk0 : 0 < k s₀ := by
    simp only [hk]; have : 2 - s₀ > 0 := by rw [hs₀']; linarith
    positivity
  have hk1 : 0 < k s₁ := by
    simp only [hk]; have : 2 - s₁ > 0 := by rw [hs₁']; linarith
    positivity
  have hc0 : 0 < c 0 := by simp only [hc]; positivity
  have hc1 : 0 < c a := by simp only [hc]; positivity
  refine ⟨c 0 * k s₀ + c a * k s₀ + c a * k s₁, by positivity, fun lam hP₀ hlam => ?_⟩
  set x := ‖lam.1‖ with hx_def
  have hx : 0 < x := norm_pos_iff.mpr hP₀
  set N := ‖lam.1‖ + ‖lam.2‖ + 1 with hN
  have hNpos : 0 < N := by positivity
  set L := ‖lam‖ ^ (β / 3) with hL
  have hL0 : 0 ≤ L := by positivity
  set Δ : ℂ → ℂ := fun P₂ => lam.2 ^ 2 - lam.1 * P₂ with hΔ
  -- step 1: the integrand bound
  set G : ℂ × ℂ → ℝ≥0∞ := fun y =>
    ENNReal.ofReal L * ‖disc (toCubic lam y)‖ₑ⁻¹ ^ (1 + 0 : ℝ) +
      ENNReal.ofReal ((‖Δ y.1‖ + N) ^ (β / 2)) * ‖disc (toCubic lam y)‖ₑ⁻¹ ^ (1 + a) with hG
  have hGm : Measurable G := by simp only [hG, hΔ]; simp_rw [disc_toCubic]; fun_prop
  have step1 : transverseMarginal β lam ≤ ∫⁻ y in ball (0 : ℂ × ℂ) 1, G y :=
    setLIntegral_mono hGm fun y hy =>
      densityBound_toCubic_le hβ0 hlam (mem_ball_zero_iff.mp hy)
  -- step 2: the `P₃`-integral
  set F : ℂ → ℝ≥0∞ := fun P₂ =>
    ENNReal.ofReal (L * (c 0 * x ^ (2 * (2 * 0 + η - 1 - 0)))) * ‖Δ P₂‖ₑ⁻¹ ^ s₀ +
      ENNReal.ofReal (c a * x ^ (2 * (2 * a + η - 1 - a))) *
        (‖Δ P₂‖ₑ⁻¹ ^ s₀ + ENNReal.ofReal (N ^ (β / 2)) * ‖Δ P₂‖ₑ⁻¹ ^ s₁) with hF
  have step2 : ∀ P₂ : ℂ, ∫⁻ P₃ in ball (0 : ℂ) 1, G (P₂, P₃) ≤ F P₂ := by
    intro P₂
    have hm0 : Measurable fun P₃ : ℂ => ‖disc (toCubic lam (P₂, P₃))‖ₑ⁻¹ ^ (1 + 0 : ℝ) := by
      simp_rw [disc_toCubic]; fun_prop
    simp only [hG]
    rw [lintegral_add_left (hm0.const_mul _), lintegral_const_mul _ hm0,
      lintegral_const_mul _ (by simp_rw [disc_toCubic]; fun_prop)]
    have I0 := lintegral_ball_inv_disc_le hP₀ P₂ le_rfl hη (by linarith)
    have I1 := lintegral_ball_inv_disc_le hP₀ P₂ ha0 hη (by linarith)
    -- the split of the Hessian weight
    have hsplit : ENNReal.ofReal ((‖Δ P₂‖ + N) ^ (β / 2)) * ‖Δ P₂‖ₑ⁻¹ ^ s₁ ≤
        ‖Δ P₂‖ₑ⁻¹ ^ s₀ + ENNReal.ofReal (N ^ (β / 2)) * ‖Δ P₂‖ₑ⁻¹ ^ s₁ := by
      have hp0 : 0 ≤ β / 2 := by positivity
      have hp1 : β / 2 ≤ 1 := by linarith
      have hadd : ENNReal.ofReal ((‖Δ P₂‖ + N) ^ (β / 2)) ≤
          ENNReal.ofReal (‖Δ P₂‖ ^ (β / 2)) + ENNReal.ofReal (N ^ (β / 2)) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0,
          ENNReal.ofReal_add (norm_nonneg _) hNpos.le,
          ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0,
          ← ENNReal.ofReal_rpow_of_nonneg hNpos.le hp0]
        exact ENNReal.rpow_add_le_add_rpow _ _ hp0 hp1
      calc ENNReal.ofReal ((‖Δ P₂‖ + N) ^ (β / 2)) * ‖Δ P₂‖ₑ⁻¹ ^ s₁
          ≤ (ENNReal.ofReal (‖Δ P₂‖ ^ (β / 2)) + ENNReal.ofReal (N ^ (β / 2))) *
              ‖Δ P₂‖ₑ⁻¹ ^ s₁ := by gcongr
        _ = ENNReal.ofReal (‖Δ P₂‖ ^ (β / 2)) * ‖Δ P₂‖ₑ⁻¹ ^ (β / 2 + s₀) +
              ENNReal.ofReal (N ^ (β / 2)) * ‖Δ P₂‖ₑ⁻¹ ^ s₁ := by
            rw [add_mul, show β / 2 + s₀ = s₁ by rw [hs₀', hs₁']]
        _ ≤ ‖Δ P₂‖ₑ⁻¹ ^ s₀ + ENNReal.ofReal (N ^ (β / 2)) * ‖Δ P₂‖ₑ⁻¹ ^ s₁ := by
            gcongr; exact ofReal_rpow_mul_inv_rpow_le _ (by positivity)
    calc ENNReal.ofReal L * (∫⁻ P₃ in ball (0 : ℂ) 1,
            ‖disc (toCubic lam (P₂, P₃))‖ₑ⁻¹ ^ (1 + 0 : ℝ)) +
          ENNReal.ofReal ((‖Δ P₂‖ + N) ^ (β / 2)) *
            ∫⁻ P₃ in ball (0 : ℂ) 1, ‖disc (toCubic lam (P₂, P₃))‖ₑ⁻¹ ^ (1 + a)
        ≤ ENNReal.ofReal L * (ENNReal.ofReal (c 0 * x ^ (2 * (2 * 0 + η - 1 - 0))) *
              ‖Δ P₂‖ₑ⁻¹ ^ s₀) +
          ENNReal.ofReal ((‖Δ P₂‖ + N) ^ (β / 2)) *
            (ENNReal.ofReal (c a * x ^ (2 * (2 * a + η - 1 - a))) * ‖Δ P₂‖ₑ⁻¹ ^ s₁) := by
          gcongr
      _ = ENNReal.ofReal (L * (c 0 * x ^ (2 * (2 * 0 + η - 1 - 0)))) * ‖Δ P₂‖ₑ⁻¹ ^ s₀ +
          ENNReal.ofReal (c a * x ^ (2 * (2 * a + η - 1 - a))) *
            (ENNReal.ofReal ((‖Δ P₂‖ + N) ^ (β / 2)) * ‖Δ P₂‖ₑ⁻¹ ^ s₁) := by
          rw [ENNReal.ofReal_mul hL0]; ring
      _ ≤ F P₂ := add_le_add le_rfl (mul_le_mul_right hsplit _)
  -- step 3: the `P₂`-integral
  have hΔm : ∀ s : ℝ, Measurable fun P₂ : ℂ => ‖Δ P₂‖ₑ⁻¹ ^ s := fun s => by
    simp only [hΔ]; fun_prop
  have J0 := lintegral_ball_inv_delta_le hP₀ lam.2 (s := s₀) (by rw [hs₀']; positivity)
    (by rw [hs₀']; linarith)
  have J1 := lintegral_ball_inv_delta_le hP₀ lam.2 (s := s₁) (by rw [hs₁']; positivity)
    (by rw [hs₁']; linarith)
  have step3 : ∫⁻ P₂ in ball (0 : ℂ) 1, F P₂ ≤
      ENNReal.ofReal (L * (c 0 * x ^ (2 * (2 * 0 + η - 1 - 0)))) *
          ENNReal.ofReal (x ^ (-s₀) * k s₀) +
        ENNReal.ofReal (c a * x ^ (2 * (2 * a + η - 1 - a))) *
          (ENNReal.ofReal (x ^ (-s₀) * k s₀) +
            ENNReal.ofReal (N ^ (β / 2)) * ENNReal.ofReal (x ^ (-s₁) * k s₁)) := by
    simp only [hF]
    rw [lintegral_add_left ((hΔm s₀).const_mul _), lintegral_const_mul _ (hΔm s₀),
      lintegral_const_mul _ (show Measurable fun P₂ => ‖Δ P₂‖ₑ⁻¹ ^ s₀ +
        ENNReal.ofReal (N ^ (β / 2)) * ‖Δ P₂‖ₑ⁻¹ ^ s₁ from (hΔm s₀).add ((hΔm s₁).const_mul _)),
      lintegral_add_left (hΔm s₀), lintegral_const_mul _ (hΔm s₁)]
    gcongr
  -- step 4: collect the real powers
  have e0 : x ^ (2 * (2 * 0 + η - 1 - 0)) * x ^ (-s₀) = x ^ (-2 + η / 2) :=
    rpow_mul_rpow_of_add hx (by rw [hs₀']; ring)
  have e1 : x ^ (2 * (2 * a + η - 1 - a)) * x ^ (-s₀) = x ^ (-2 + β / 3 + η / 2) :=
    rpow_mul_rpow_of_add hx (by rw [hs₀', ha_def]; ring)
  have e2 : x ^ (2 * (2 * a + η - 1 - a)) * x ^ (-s₁) = x ^ (-2 - β / 6 + η / 2) :=
    rpow_mul_rpow_of_add hx (by rw [hs₁', ha_def]; ring)
  refine step1.trans ?_
  rw [setLIntegral_ball_prod hGm]
  refine ((lintegral_mono fun P₂ => step2 P₂).trans step3).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set t₁ := L * x ^ (-2 + η / 2)
  set t₂ := x ^ (-2 + β / 3 + η / 2)
  set t₃ := N ^ (β / 2) * x ^ (-2 - β / 6 + η / 2)
  have ht₁ : 0 ≤ t₁ := by positivity
  have ht₂ : 0 ≤ t₂ := by positivity
  have ht₃ : 0 ≤ t₃ := by positivity
  have hp₁ : 0 ≤ c 0 * k s₀ := by positivity
  have hp₂ : 0 ≤ c a * k s₀ := by positivity
  have hp₃ : 0 ≤ c a * k s₁ := by positivity
  calc L * (c 0 * x ^ (2 * (2 * 0 + η - 1 - 0))) * (x ^ (-s₀) * k s₀) +
        c a * x ^ (2 * (2 * a + η - 1 - a)) *
          (x ^ (-s₀) * k s₀ + N ^ (β / 2) * (x ^ (-s₁) * k s₁))
      = c 0 * k s₀ * t₁ + c a * k s₀ * t₂ + c a * k s₁ * t₃ := by
        simp only [t₁, t₂, t₃, ← e0, ← e1, ← e2]; ring
    _ ≤ (c 0 * k s₀ + c a * k s₀ + c a * k s₁) * t₁ +
          (c 0 * k s₀ + c a * k s₀ + c a * k s₁) * t₂ +
          (c 0 * k s₀ + c a * k s₀ + c a * k s₁) * t₃ := by
        gcongr <;> linarith
    _ = _ := by ring

/-- `(3/4 · y³)^{-t} = (3/4)^{-t} y^{-3t}`. -/
private lemma rpow_three_quarters {y : ℝ} (hy : 0 < y) (t : ℝ) :
    (3 / 4 * y ^ 3) ^ (-t) = (3 / 4) ^ (-t) * y ^ (-(3 * t)) := by
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul hy.le]
  push_cast; ring_nf

/-- The ball constant `2π/(2-s) + π` of `lintegral_ball_sub_inv_rpow_le`. -/
noncomputable def ballConst (s : ℝ) : ℝ := 2 * π / (2 - s) + π

/-- `ballConst s > 0` for `s < 2`. -/
theorem ballConst_pos {s : ℝ} (hs : s < 2) : 0 < ballConst s := by
  unfold ballConst; have : 0 < 2 - s := by linarith
  positivity

/-- The exponent bookkeeping of `transverseMarginal_le_outer`. -/
private lemma outer_identity {y β a c k₀ k₁ : ℝ} (hy0 : 0 < y) (ha : a = β / 6) :
    (y ^ (β / 2) * ((3 / 4 * y ^ 3) ^ (-(1 + 0 : ℝ)) * k₀) +
        (4 * y ^ 2) ^ (β / 2) * ((3 / 4 * y ^ 3) ^ (-(1 + a)) * k₁)) * c =
      c * ((3 / 4) ^ (-(1 + 0 : ℝ)) * k₀ + 4 ^ (β / 2) * (3 / 4) ^ (-(1 + a)) * k₁) *
        y ^ (β / 2 - 3) := by
  rw [rpow_three_quarters hy0, rpow_three_quarters hy0,
    Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast y 2,
    ← Real.rpow_mul hy0.le]
  have r1 : y ^ (β / 2) * y ^ (-(3 * (1 + 0 : ℝ))) = y ^ (β / 2 - 3) :=
    rpow_mul_rpow_of_add hy0 (by ring)
  have r2 : y ^ (((2 : ℕ) : ℝ) * (β / 2)) * y ^ (-(3 * (1 + a))) = y ^ (β / 2 - 3) :=
    rpow_mul_rpow_of_add hy0 (by rw [ha]; push_cast; ring)
  linear_combination (c * ((3 / 4) ^ (-(1 + 0 : ℝ)) * k₀)) * r1 +
    (c * (4 ^ (β / 2) * (3 / 4) ^ (-(1 + a)) * k₁)) * r2

/-- **The outer bound**: on the region `|P₁| ≥ 1`, `6|P₀| ≤ |P₁|²`, `8|P₀|² ≤ |P₁|³`,
`m_β(λ) ≤ K |P₁|^{β/2 - 3}`. Here `∂𝔇/∂P₃ = B = 4P₁³ - 6P₀P₁P₂` dominates the leading coefficient
`P₀²`, so the estimate holds uniformly as `P₀ → 0` (the note's directions near `P₀ = 0`) and for
every `‖λ‖ ≥ 1`. In the note's chart `φ = P₁/P₀`, `ε = 1/|P₀|`, this is (outer):
`ρ^{β/3} ε^{3-α} |φ|^{-3+3α} = |P₁|^{-3+3α}` with `α = β/6`. -/
theorem transverseMarginal_le_outer {β : ℝ} (hβ0 : 0 ≤ β) (hβ2 : β < 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lam : ℂ × ℂ, 1 ≤ ‖lam.2‖ → 6 * ‖lam.1‖ ≤ ‖lam.2‖ ^ 2 →
      8 * ‖lam.1‖ ^ 2 ≤ ‖lam.2‖ ^ 3 →
        transverseMarginal β lam ≤ ENNReal.ofReal (K * ‖lam.2‖ ^ (β / 2 - 3)) := by
  set a := β / 6 with ha_def
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a < 1 / 3 := by rw [ha_def]; linarith
  have hk0 : 0 < ballConst (1 + 0) := ballConst_pos (by norm_num)
  have hk1 : 0 < ballConst (1 + a) := ballConst_pos (by linarith)
  refine ⟨π * ((3 / 4) ^ (-(1 + 0 : ℝ)) * ballConst (1 + 0) +
    4 ^ (β / 2) * (3 / 4) ^ (-(1 + a)) * ballConst (1 + a)), by positivity,
    fun lam h1 h6 h8 => ?_⟩
  set x := ‖lam.1‖ with hx_def
  set y := ‖lam.2‖ with hy_def
  have hx0 : 0 ≤ x := norm_nonneg _
  have hy0 : 0 < y := by linarith
  have hlam : 1 ≤ ‖lam‖ := h1.trans (norm_snd_le lam)
  set N := ‖lam.1‖ + ‖lam.2‖ + 1 with hN
  set L := ‖lam‖ ^ (β / 3) with hL
  have hL0 : 0 ≤ L := by positivity
  set Δ : ℂ → ℂ := fun P₂ => lam.2 ^ 2 - lam.1 * P₂ with hΔ
  set G : ℂ × ℂ → ℝ≥0∞ := fun y =>
    ENNReal.ofReal L * ‖disc (toCubic lam y)‖ₑ⁻¹ ^ (1 + 0 : ℝ) +
      ENNReal.ofReal ((‖Δ y.1‖ + N) ^ (β / 2)) * ‖disc (toCubic lam y)‖ₑ⁻¹ ^ (1 + a) with hG
  have hGm : Measurable G := by simp only [hG, hΔ]; simp_rw [disc_toCubic]; fun_prop
  have step1 : transverseMarginal β lam ≤ ∫⁻ y in ball (0 : ℂ × ℂ) 1, G y :=
    setLIntegral_mono hGm fun y hy =>
      densityBound_toCubic_le hβ0 hlam (mem_ball_zero_iff.mp hy)
  -- the weights on the box
  have hLb : L ≤ y ^ (β / 2) := by
    have hn : ‖lam‖ ^ 2 ≤ y ^ 3 := by
      rw [Prod.norm_def]
      rcases le_total x y with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith
    calc L = (‖lam‖ ^ 2) ^ (β / 6) := by
          rw [hL, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; congr 1; push_cast; ring
      _ ≤ (y ^ 3) ^ (β / 6) := by gcongr
      _ = y ^ (β / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; congr 1; push_cast; ring
  set M := y ^ (β / 2) * ((3 / 4 * y ^ 3) ^ (-(1 + 0 : ℝ)) * ballConst (1 + 0)) +
    (4 * y ^ 2) ^ (β / 2) * ((3 / 4 * y ^ 3) ^ (-(1 + a)) * ballConst (1 + a)) with hM
  have step2 : ∀ P₂ ∈ ball (0 : ℂ) 1, ∫⁻ P₃ in ball (0 : ℂ) 1, G (P₂, P₃) ≤ ENNReal.ofReal M := by
    intro P₂ hP₂
    rw [mem_ball_zero_iff] at hP₂
    have hz := norm_nonneg P₂
    set B := 4 * lam.2 ^ 3 - 6 * lam.1 * lam.2 * P₂ with hB_def
    have hB : 3 * y ^ 3 ≤ ‖B‖ := by
      have : ‖6 * lam.1 * lam.2 * P₂‖ ≤ y ^ 3 := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
        nlinarith [mul_le_mul_of_nonneg_left hP₂.le (by positivity : 0 ≤ 6 * x * y)]
      have h4 : ‖(4 : ℂ) * lam.2 ^ 3‖ = 4 * y ^ 3 := by
        rw [norm_mul, norm_pow, Complex.norm_ofNat]
      have := norm_sub_norm_le ((4 : ℂ) * lam.2 ^ 3) (6 * lam.1 * lam.2 * P₂)
      linarith
    have hB0 : B ≠ 0 := by
      intro h; rw [h, norm_zero] at hB; have : 0 < y ^ 3 := by positivity
      linarith
    have hAB : 8 * ‖lam.1 ^ 2‖ ≤ ‖B‖ := by
      rw [norm_pow]; nlinarith [pow_pos hy0 3]
    have hBq : 3 / 4 * y ^ 3 ≤ ‖B‖ / 4 := by linarith
    have hI : ∀ t : ℝ, 0 ≤ t → t < 1 →
        ∫⁻ P₃ in ball (0 : ℂ) 1, ‖disc (toCubic lam (P₂, P₃))‖ₑ⁻¹ ^ (1 + t) ≤
          ENNReal.ofReal ((3 / 4 * y ^ 3) ^ (-(1 + t)) * ballConst (1 + t)) := by
      intro t ht0 ht1
      simp_rw [disc_toCubic]
      refine (lintegral_ball_one_inv_quadratic_le hB0 hAB (by linarith) (by linarith)).trans ?_
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_
        (ballConst_pos (by linarith)).le)
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hBq (by linarith)
    have hHb : ‖Δ P₂‖ + N ≤ 4 * y ^ 2 := by
      have : ‖Δ P₂‖ ≤ y ^ 2 + x := by
        simp only [hΔ]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_pow, norm_mul]; nlinarith
      have hyy : y ≤ y ^ 2 := by nlinarith
      have h1y : 1 ≤ y ^ 2 := by nlinarith
      linarith [hN]
    have hm0 : Measurable fun P₃ : ℂ => ‖disc (toCubic lam (P₂, P₃))‖ₑ⁻¹ ^ (1 + 0 : ℝ) := by
      simp_rw [disc_toCubic]; fun_prop
    simp only [hG]
    rw [lintegral_add_left (hm0.const_mul _), lintegral_const_mul _ hm0,
      lintegral_const_mul _ (by simp_rw [disc_toCubic]; fun_prop)]
    calc ENNReal.ofReal L * (∫⁻ P₃ in ball (0 : ℂ) 1,
            ‖disc (toCubic lam (P₂, P₃))‖ₑ⁻¹ ^ (1 + 0 : ℝ)) +
          ENNReal.ofReal ((‖Δ P₂‖ + N) ^ (β / 2)) *
            ∫⁻ P₃ in ball (0 : ℂ) 1, ‖disc (toCubic lam (P₂, P₃))‖ₑ⁻¹ ^ (1 + a)
        ≤ ENNReal.ofReal (y ^ (β / 2)) *
            ENNReal.ofReal ((3 / 4 * y ^ 3) ^ (-(1 + 0 : ℝ)) * ballConst (1 + 0)) +
          ENNReal.ofReal ((4 * y ^ 2) ^ (β / 2)) *
            ENNReal.ofReal ((3 / 4 * y ^ 3) ^ (-(1 + a)) * ballConst (1 + a)) := by
          gcongr
          · exact hI 0 le_rfl (by norm_num)
          · exact hI a ha0 (by linarith)
      _ = ENNReal.ofReal M := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine step1.trans ?_
  rw [setLIntegral_ball_prod hGm]
  refine (setLIntegral_mono measurable_const step2).trans ?_
  rw [setLIntegral_const, Complex.volume_ball, ENNReal.ofReal_one, one_pow, one_mul,
    show ((NNReal.pi : ℝ≥0∞)) = ENNReal.ofReal π by
      rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi],
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (outer_identity hy0 ha_def))

end SLT.PositionFour.Downstream
