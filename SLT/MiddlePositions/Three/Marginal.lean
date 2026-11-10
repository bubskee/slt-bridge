/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Three.Suffix
public import SLT.PositionFour.Downstream.Finiteness
public import SLT.MiddlePositions.Toolkit.Quadratic

/-!
# The two-cube transverse marginal at position three

The note's Lemma "Pointwise bounds on explicit regions" (Section 5 of
`complex_middle_positions.tex`). Write `P = (λ, y)` with `λ = (U, V) = (P₀, P₁)` and
`y = (u, v) = (P₂, P₃)`, and put `x = |U|`, `y = |V|`. The marginal is
`m(λ) = ∫_{|u|, |v| < 1} F(U, V, u, v)` (`marginal`). As a quadratic in `v`,
`𝔇 = U² v² + (4V³ - 6UVu) v + (4Uu³ - 3V²u²)`, with `v`-discriminant `16 (V² - Uu)³`.

* `marginal_le_outer` (outer region `y ≥ 16`, `256 x² ≤ y³`, i.e. the note's `x ≤ y^{3/2}/16`):
  `m ≤ K y^{-15/4}`, by the one-dominant-root inequality of `PositionFour`, valid at `U = 0`;
* `marginal_le_central` (`x ≥ 1`, `y ≤ 16 x`): `m ≤ K x^{-17/8}`, by `FullPlaneQuadratic` in `v`
  and the shifted-disc bound in `u`;
* `lintegral_marginal_near_lt_top`: `∫_{‖λ‖ < 64} m < ∞`, from `LocallyIntegrableF`;
* `lintegral_marginal_far_sq_lt_top`: `∫_{‖λ‖ ≥ 64} m² < ∞`.

The near part is only used in `L¹`; it is never squared.

**Departure from the note.** The central region is enlarged to `{x ≥ 1, y ≤ 16x}` (the note uses
`y ≤ (16x)^{2/3}`), and the outer region of integration to `{y ≥ 16, x ≤ y²}` (the note uses
`x ≤ y^{3/2}/16`). The square integrals then reduce to `∫_{|U| ≥ 1} |U|^{-9/4}` and
`∫_{|V| ≥ 16} |V|^{-7/2}`, still finite, with no fractional radii.
-/

@[expose] public section

namespace SLT.MiddlePositions.Three

open MeasureTheory Set Real Metric SLT.PositionFour SLT.PositionFour.Downstream SLT.Pushforward
open scoped ENNReal NNReal

/-! ### The bounding density and planar volumes -/

/-- `F` in terms of extended inverse powers of `|𝔇|`. -/
theorem F_eq (P : Cubic) :
    F P = ‖disc P‖ₑ⁻¹ ^ (4 / 3 : ℝ) +
      ENNReal.ofReal (‖P‖ ^ (1 / 4 : ℝ)) * ‖disc P‖ₑ⁻¹ ^ (11 / 8 : ℝ) := by
  rw [F, twoCubeDensity, enorm_eq_nnnorm]

/-- `F` is measurable. -/
theorem measurable_F : Measurable F := by
  have := continuous_disc.measurable
  unfold F; fun_prop

/-! ### The marginal -/

/-- The transverse marginal `m(λ) = ∫_{|P₂|, |P₃| < 1} F(λ, P₂, P₃)` (sup norm on `(P₂, P₃)`). -/
noncomputable def marginal (lam : ℂ × ℂ) : ℝ≥0∞ :=
  ∫⁻ y in ball (0 : ℂ × ℂ) 1, F (toCubic lam y)

/-- The marginal is measurable. -/
theorem measurable_marginal : Measurable marginal :=
  (measurable_F.comp measurable_toCubic).lintegral_prod_right'

/-- The box integral `∫_{|P₂|, |P₃| < 1} |𝔇(λ, y)|^{-t} dy`. -/
noncomputable def discInt (t : ℝ) (lam : ℂ × ℂ) : ℝ≥0∞ :=
  ∫⁻ y in ball (0 : ℂ × ℂ) 1, ‖disc (toCubic lam y)‖ₑ⁻¹ ^ t

/-- The integrand of `discInt` is measurable. -/
theorem measurable_disc_toCubic_inv (lam : ℂ × ℂ) (t : ℝ) :
    Measurable fun y : ℂ × ℂ => ‖disc (toCubic lam y)‖ₑ⁻¹ ^ t :=
  ((continuous_disc.measurable.comp (measurable_toCubic.comp
    (measurable_const.prodMk measurable_id))).enorm.inv).pow_const t

/-- On the box, `‖P‖ ≤ N` once `|P₀|, |P₁| ≤ N` and `N ≥ 1`. -/
theorem norm_toCubic_le_of {lam y : ℂ × ℂ} {N : ℝ} (hN : 1 ≤ N) (h1 : ‖lam.1‖ ≤ N)
    (h2 : ‖lam.2‖ ≤ N) (hy : ‖y‖ < 1) : ‖toCubic lam y‖ ≤ N := by
  refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun i => ?_
  have h3 := norm_fst_le y; have h4 := norm_snd_le y
  fin_cases i <;> simp [toCubic] <;> linarith

/-- **The marginal through the two box integrals**: if `‖P‖ ≤ N` on the box, then
`m(λ) ≤ ∫ |𝔇|^{-4/3} + N^{1/4} ∫ |𝔇|^{-11/8}`. -/
theorem marginal_le (lam : ℂ × ℂ) {N : ℝ} (hN : 1 ≤ N) (h1 : ‖lam.1‖ ≤ N) (h2 : ‖lam.2‖ ≤ N) :
    marginal lam ≤
      discInt (4 / 3) lam + ENNReal.ofReal (N ^ (1 / 4 : ℝ)) * discInt (11 / 8) lam := by
  rw [discInt, discInt, ← lintegral_const_mul _ (measurable_disc_toCubic_inv _ _),
    ← lintegral_add_left (measurable_disc_toCubic_inv _ _)]
  refine setLIntegral_mono ((measurable_disc_toCubic_inv _ _).add
    ((measurable_disc_toCubic_inv _ _).const_mul _)) fun y hy => ?_
  rw [F_eq]
  gcongr
  exact norm_toCubic_le_of hN h1 h2 (mem_ball_zero_iff.mp hy)

/-- The box integral as an iterated integral of a quadratic in `v = P₃`. -/
theorem discInt_eq (t : ℝ) (lam : ℂ × ℂ) :
    discInt t lam = ∫⁻ u in ball (0 : ℂ) 1, ∫⁻ v in ball (0 : ℂ) 1,
      ‖lam.1 ^ 2 * v ^ 2 + (4 * lam.2 ^ 3 - 6 * lam.1 * lam.2 * u) * v +
        (4 * lam.1 * u ^ 3 - 3 * lam.2 ^ 2 * u ^ 2)‖ₑ⁻¹ ^ t := by
  rw [discInt, setLIntegral_ball_prod (measurable_disc_toCubic_inv lam t)]
  simp_rw [disc_toCubic]

/-! ### The outer region -/

/-- `(3/4 · y³)^{-t} = (3/4)^{-t} y^{-3t}`. -/
theorem rpow_three_quarters_mul {y : ℝ} (hy : 0 < y) (t : ℝ) :
    (3 / 4 * y ^ 3) ^ (-t) = (3 / 4) ^ (-t) * y ^ (-(3 * t)) := by
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul hy.le]
  push_cast; ring_nf

/-- **The box integral on the outer region** `|V| ≥ 16`, `256 |U|² ≤ |V|³`: the `v`-quadratic
has a dominant linear coefficient, `|B| ≥ 3|V|³ ≥ 8|U|²`, uniformly on `|u| < 1`. -/
theorem discInt_le_outer {lam : ℂ × ℂ} {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2)
    (h16 : 16 ≤ ‖lam.2‖) (h256 : 256 * ‖lam.1‖ ^ 2 ≤ ‖lam.2‖ ^ 3) :
    discInt t lam ≤ ENNReal.ofReal (π * ((3 / 4 * ‖lam.2‖ ^ 3) ^ (-t) * ballConst t)) := by
  set x := ‖lam.1‖ with hx_def
  set y := ‖lam.2‖ with hy_def
  have hx0 : 0 ≤ x := norm_nonneg _
  have hy0 : 0 < y := by linarith
  have h6 : 6 * x ≤ y ^ 2 := by nlinarith [sq_nonneg (6 * x - y ^ 2), sq_nonneg (6 * x + y ^ 2)]
  have hk : 0 < ballConst t := ballConst_pos ht2
  rw [discInt_eq]
  have step : ∀ u ∈ ball (0 : ℂ) 1, ∫⁻ v in ball (0 : ℂ) 1,
      ‖lam.1 ^ 2 * v ^ 2 + (4 * lam.2 ^ 3 - 6 * lam.1 * lam.2 * u) * v +
        (4 * lam.1 * u ^ 3 - 3 * lam.2 ^ 2 * u ^ 2)‖ₑ⁻¹ ^ t ≤
        ENNReal.ofReal ((3 / 4 * y ^ 3) ^ (-t) * ballConst t) := by
    intro u hu
    rw [mem_ball_zero_iff] at hu
    have hz := norm_nonneg u
    set B := 4 * lam.2 ^ 3 - 6 * lam.1 * lam.2 * u with hB_def
    have hB : 3 * y ^ 3 ≤ ‖B‖ := by
      have : ‖6 * lam.1 * lam.2 * u‖ ≤ y ^ 3 := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
        nlinarith [mul_le_mul_of_nonneg_left hu.le (by positivity : 0 ≤ 6 * x * y)]
      have h4 : ‖(4 : ℂ) * lam.2 ^ 3‖ = 4 * y ^ 3 := by
        rw [norm_mul, norm_pow, Complex.norm_ofNat]
      have := norm_sub_norm_le ((4 : ℂ) * lam.2 ^ 3) (6 * lam.1 * lam.2 * u)
      linarith
    have hB0 : B ≠ 0 := by
      intro h; rw [h, norm_zero] at hB; have : 0 < y ^ 3 := by positivity
      linarith
    have hAB : 8 * ‖lam.1 ^ 2‖ ≤ ‖B‖ := by
      rw [norm_pow]; nlinarith [pow_pos hy0 3]
    have hBq : 3 / 4 * y ^ 3 ≤ ‖B‖ / 4 := by linarith
    refine (lintegral_ball_one_inv_quadratic_le hB0 hAB ht0 ht2).trans ?_
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hk.le)
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hBq (by linarith)
  refine (setLIntegral_mono measurable_const step).trans ?_
  rw [setLIntegral_const, volume_ball_one_complex, ← ENNReal.ofReal_mul (by positivity), mul_comm]

/-- **Outer bound** (the note's `𝒪`, including `U = 0`): on `|V| ≥ 16`, `256 |U|² ≤ |V|³`,
`m(U, V) ≤ K |V|^{-15/4}`. -/
theorem marginal_le_outer :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lam : ℂ × ℂ, 16 ≤ ‖lam.2‖ → 256 * ‖lam.1‖ ^ 2 ≤ ‖lam.2‖ ^ 3 →
      marginal lam ≤ ENNReal.ofReal (K * ‖lam.2‖ ^ (-(15 / 4) : ℝ)) := by
  have hk1 : 0 < ballConst (4 / 3) := ballConst_pos (by norm_num)
  have hk2 : 0 < ballConst (11 / 8) := ballConst_pos (by norm_num)
  refine ⟨π * ((3 / 4) ^ (-(4 / 3) : ℝ) * ballConst (4 / 3) +
    (3 / 4) ^ (-(11 / 8) : ℝ) * ballConst (11 / 8)), by positivity, fun lam h16 h256 => ?_⟩
  set x := ‖lam.1‖ with hx_def
  set y := ‖lam.2‖ with hy_def
  have hx0 : 0 ≤ x := norm_nonneg _
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  set N := y ^ (3 / 2 : ℝ) with hN_def
  have hN2 : N ^ 2 = y ^ 3 := by
    rw [hN_def, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
  have hN0 : 0 ≤ N := by positivity
  have hyN : y ≤ N := by
    have := Real.rpow_le_rpow_of_exponent_le hy1 (show (1 : ℝ) ≤ 3 / 2 by norm_num)
    rwa [Real.rpow_one] at this
  have hxN : x ≤ N := by nlinarith
  have hN14 : N ^ (1 / 4 : ℝ) = y ^ (3 / 8 : ℝ) := by
    rw [hN_def, ← Real.rpow_mul hy0.le]; norm_num
  refine (marginal_le lam (hy1.trans hyN) hxN hyN).trans ?_
  refine (add_le_add (discInt_le_outer (by norm_num) (by norm_num) h16 h256)
    (mul_le_mul_right (discInt_le_outer (by norm_num) (by norm_num) h16 h256) _)).trans ?_
  rw [hN14, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
    (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [rpow_three_quarters_mul hy0, rpow_three_quarters_mul hy0]
  have e1 : y ^ (-(3 * (4 / 3)) : ℝ) ≤ y ^ (-(15 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
  have e2 : y ^ (3 / 8 : ℝ) * y ^ (-(3 * (11 / 8)) : ℝ) = y ^ (-(15 / 4) : ℝ) := by
    rw [← Real.rpow_add hy0]; norm_num
  have hp1 : 0 ≤ (3 / 4 : ℝ) ^ (-(4 / 3) : ℝ) := by positivity
  have hp2 : 0 ≤ (3 / 4 : ℝ) ^ (-(11 / 8) : ℝ) := by positivity
  calc π * ((3 / 4) ^ (-(4 / 3) : ℝ) * y ^ (-(3 * (4 / 3)) : ℝ) * ballConst (4 / 3)) +
        y ^ (3 / 8 : ℝ) * (π * ((3 / 4) ^ (-(11 / 8) : ℝ) * y ^ (-(3 * (11 / 8)) : ℝ) *
          ballConst (11 / 8)))
      = π * (3 / 4) ^ (-(4 / 3) : ℝ) * ballConst (4 / 3) * y ^ (-(3 * (4 / 3)) : ℝ) +
          π * (3 / 4) ^ (-(11 / 8) : ℝ) * ballConst (11 / 8) *
            (y ^ (3 / 8 : ℝ) * y ^ (-(3 * (11 / 8)) : ℝ)) := by ring
    _ ≤ π * (3 / 4) ^ (-(4 / 3) : ℝ) * ballConst (4 / 3) * y ^ (-(15 / 4) : ℝ) +
          π * (3 / 4) ^ (-(11 / 8) : ℝ) * ballConst (11 / 8) * y ^ (-(15 / 4) : ℝ) := by
        rw [e2]; gcongr
    _ = _ := by ring

/-! ### The central region -/

/-- **The box integral on the central region** (`U ≠ 0`, `1 < t`, `3(t - 1) < 2`): integrating
`v` over all of `ℂ` with `FullPlaneQuadratic`, then `u` over the unit disc,
`∫ |𝔇|^{-t} ≤ K 16^{1-t} c |U|^{-(t+1)}`. -/
theorem discInt_le_central {t K : ℝ} (ht1 : 1 < t) (ht3 : 3 * (t - 1) < 2) (hK0 : 0 ≤ K)
    (hK : FullPlaneQuadratic t K) {lam : ℂ × ℂ} (hU : lam.1 ≠ 0) :
    discInt t lam ≤ ENNReal.ofReal (K * 16 ^ (-(t - 1)) * ballConst (3 * (t - 1)) *
      ‖lam.1‖ ^ (-(t + 1))) := by
  set x := ‖lam.1‖ with hx_def
  have hx0 : 0 < x := norm_pos_iff.mpr hU
  have hk : 0 < ballConst (3 * (t - 1)) := ballConst_pos ht3
  rw [discInt_eq]
  have step : ∀ u : ℂ, ∫⁻ v in ball (0 : ℂ) 1,
      ‖lam.1 ^ 2 * v ^ 2 + (4 * lam.2 ^ 3 - 6 * lam.1 * lam.2 * u) * v +
        (4 * lam.1 * u ^ 3 - 3 * lam.2 ^ 2 * u ^ 2)‖ₑ⁻¹ ^ t ≤
        ENNReal.ofReal (K * x ^ (2 * (t - 2)) * 16 ^ (-(t - 1))) *
          ‖lam.2 ^ 2 - lam.1 * u‖ₑ⁻¹ ^ (3 * (t - 1)) := by
    intro u
    refine (setLIntegral_le_lintegral _ _).trans ?_
    refine (hK _ _ _ (pow_ne_zero 2 hU)).trans (le_of_eq ?_)
    rw [discr_disc, enorm_mul_inv_rpow (by norm_num) _ (by linarith), enorm_pow_inv_rpow,
      ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), norm_pow, ← hx_def,
      ← Real.rpow_natCast x 2, ← Real.rpow_mul hx0.le]
    norm_num
  calc ∫⁻ u in ball (0 : ℂ) 1, ∫⁻ v in ball (0 : ℂ) 1,
        ‖lam.1 ^ 2 * v ^ 2 + (4 * lam.2 ^ 3 - 6 * lam.1 * lam.2 * u) * v +
          (4 * lam.1 * u ^ 3 - 3 * lam.2 ^ 2 * u ^ 2)‖ₑ⁻¹ ^ t
      ≤ ∫⁻ u in ball (0 : ℂ) 1, ENNReal.ofReal (K * x ^ (2 * (t - 2)) * 16 ^ (-(t - 1))) *
          ‖lam.2 ^ 2 - lam.1 * u‖ₑ⁻¹ ^ (3 * (t - 1)) :=
        setLIntegral_mono (by fun_prop) fun u _ => step u
    _ = ENNReal.ofReal (K * x ^ (2 * (t - 2)) * 16 ^ (-(t - 1))) *
          ∫⁻ u in ball (0 : ℂ) 1, ‖lam.2 ^ 2 - lam.1 * u‖ₑ⁻¹ ^ (3 * (t - 1)) :=
        lintegral_const_mul _ (by fun_prop)
    _ ≤ ENNReal.ofReal (K * x ^ (2 * (t - 2)) * 16 ^ (-(t - 1))) *
          ENNReal.ofReal (x ^ (-(3 * (t - 1))) * (2 * π / (2 - 3 * (t - 1)) + π)) := by
        gcongr; exact lintegral_ball_inv_delta_le hU _ (by linarith) ht3
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : x ^ (2 * (t - 2)) * x ^ (-(3 * (t - 1))) = x ^ (-(t + 1)) := by
          rw [← Real.rpow_add hx0]; ring_nf
        rw [ballConst, ← this]; ring

/-- **Central bound**: on `|U| ≥ 1`, `|V| ≤ 16 |U|`, `m(U, V) ≤ K |U|^{-17/8}`. -/
theorem marginal_le_central {K₁ K₂ : ℝ} (hK₁ : FullPlaneQuadratic (4 / 3) K₁)
    (hK₂ : FullPlaneQuadratic (11 / 8) K₂) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lam : ℂ × ℂ, 1 ≤ ‖lam.1‖ → ‖lam.2‖ ≤ 16 * ‖lam.1‖ →
      marginal lam ≤ ENNReal.ofReal (K * ‖lam.1‖ ^ (-(17 / 8) : ℝ)) := by
  set L₁ := max K₁ 0
  set L₂ := max K₂ 0
  have hL₁ : 0 ≤ L₁ := le_max_right _ _
  have hL₂ : 0 ≤ L₂ := le_max_right _ _
  have hQ₁ := fullPlaneQuadratic_mono hK₁ (le_max_left K₁ 0)
  have hQ₂ := fullPlaneQuadratic_mono hK₂ (le_max_left K₂ 0)
  set c₁ := L₁ * 16 ^ (-(4 / 3 - 1) : ℝ) * ballConst (3 * (4 / 3 - 1))
  set c₂ := L₂ * 16 ^ (-(11 / 8 - 1) : ℝ) * ballConst (3 * (11 / 8 - 1))
  have hc₁ : 0 ≤ c₁ := mul_nonneg (by positivity) (ballConst_pos (by norm_num)).le
  have hc₂ : 0 ≤ c₂ := mul_nonneg (by positivity) (ballConst_pos (by norm_num)).le
  refine ⟨c₁ + 16 ^ (1 / 4 : ℝ) * c₂, by positivity, fun lam hx1 hy => ?_⟩
  set x := ‖lam.1‖ with hx_def
  have hx0 : 0 < x := by linarith
  have hU : lam.1 ≠ 0 := norm_pos_iff.mp hx0
  refine (marginal_le lam (N := 16 * x) (by linarith) (by linarith) hy).trans ?_
  refine (add_le_add (discInt_le_central (by norm_num) (by norm_num) hL₁ hQ₁ hU)
    (mul_le_mul_right (discInt_le_central (by norm_num) (by norm_num) hL₂ hQ₂ hU) _)).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
    (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e1 : x ^ (-(4 / 3 + 1) : ℝ) ≤ x ^ (-(17 / 8) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have e2 : (16 * x) ^ (1 / 4 : ℝ) * x ^ (-(11 / 8 + 1) : ℝ) =
      16 ^ (1 / 4 : ℝ) * x ^ (-(17 / 8) : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hx0.le, mul_assoc, ← Real.rpow_add hx0]; norm_num
  calc c₁ * x ^ (-(4 / 3 + 1) : ℝ) + (16 * x) ^ (1 / 4 : ℝ) * (c₂ * x ^ (-(11 / 8 + 1) : ℝ))
      = c₁ * x ^ (-(4 / 3 + 1) : ℝ) + c₂ * ((16 * x) ^ (1 / 4 : ℝ) * x ^ (-(11 / 8 + 1) : ℝ)) := by
        ring
    _ ≤ c₁ * x ^ (-(17 / 8) : ℝ) + c₂ * (16 ^ (1 / 4 : ℝ) * x ^ (-(17 / 8) : ℝ)) := by
        rw [e2]; gcongr
    _ = _ := by ring

/-! ### The near part in `L¹` -/

/-- **The near part is integrable**: `∫_{‖λ‖ < 64} m ≤ ∫_{‖P‖ ≤ 64} F < ∞`. -/
theorem lintegral_marginal_near_lt_top (hF : LocallyIntegrableF) :
    ∫⁻ lam in ball (0 : ℂ × ℂ) 64, marginal lam < ∞ := by
  have hG : Measurable ((closedBall (0 : Cubic) 64).indicator F) :=
    measurable_F.indicator measurableSet_closedBall
  have hpt : ∀ lam : ℂ × ℂ, (ball (0 : ℂ × ℂ) 64).indicator marginal lam ≤
      ∫⁻ y, (closedBall (0 : Cubic) 64).indicator F (toCubic lam y) := by
    intro lam
    by_cases hl : lam ∈ ball (0 : ℂ × ℂ) 64
    · rw [indicator_of_mem hl, marginal, ← lintegral_indicator measurableSet_ball]
      refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ ball (0 : ℂ × ℂ) 1
      · rw [indicator_of_mem hy, indicator_of_mem]
        rw [mem_ball_zero_iff] at hl hy
        rw [mem_closedBall_zero_iff]
        exact norm_toCubic_le_of (by norm_num) ((norm_fst_le lam).trans hl.le)
          ((norm_snd_le lam).trans hl.le) hy
      · rw [indicator_of_notMem hy]; exact bot_le
    · rw [indicator_of_notMem hl]; exact bot_le
  calc ∫⁻ lam in ball (0 : ℂ × ℂ) 64, marginal lam
      = ∫⁻ lam, (ball (0 : ℂ × ℂ) 64).indicator marginal lam :=
        (lintegral_indicator measurableSet_ball _).symm
    _ ≤ ∫⁻ lam, ∫⁻ y, (closedBall (0 : Cubic) 64).indicator F (toCubic lam y) :=
        lintegral_mono hpt
    _ = ∫⁻ P, (closedBall (0 : Cubic) 64).indicator F P := (lintegral_cubic hG).symm
    _ = ∫⁻ P in closedBall (0 : Cubic) 64, F P := lintegral_indicator measurableSet_closedBall _
    _ < ∞ := hF 64

/-! ### The far part in `L²` -/

/-- The enlarged outer region `{|V| ≥ 16, |U| ≤ |V|²}`. -/
def outerRegion : Set (ℂ × ℂ) := {lam | 16 ≤ ‖lam.2‖ ∧ ‖lam.1‖ ≤ ‖lam.2‖ ^ 2}

/-- The enlarged central region `{|U| ≥ 1, |V| ≤ 16 |U|}`. -/
def centralRegion : Set (ℂ × ℂ) := {lam | 1 ≤ ‖lam.1‖ ∧ ‖lam.2‖ ≤ 16 * ‖lam.1‖}

/-- The outer region is measurable. -/
theorem measurableSet_outerRegion : MeasurableSet outerRegion :=
  (measurableSet_le (f := fun lam : ℂ × ℂ => (16 : ℝ)) measurable_const (by fun_prop)).inter
    (measurableSet_le (f := fun lam : ℂ × ℂ => ‖lam.1‖) (by fun_prop) (by fun_prop))

/-- The central region is measurable. -/
theorem measurableSet_centralRegion : MeasurableSet centralRegion :=
  (measurableSet_le (f := fun lam : ℂ × ℂ => (1 : ℝ)) measurable_const (by fun_prop)).inter
    (measurableSet_le (f := fun lam : ℂ × ℂ => ‖lam.2‖) (by fun_prop) (by fun_prop))

/-- `(K y^{-r})² = K² y^{-2r}`. -/
private lemma sq_mul_rpow {K y r : ℝ} (hy : 0 ≤ y) :
    (K * y ^ (-r)) ^ 2 = K ^ 2 * y ^ (-(2 * r)) := by
  rw [mul_pow, ← Real.rpow_natCast (y ^ (-r)), ← Real.rpow_mul hy]; congr 2; push_cast; ring

/-- **The far region splits into the two explicit regions**: on `‖λ‖ ≥ 64`,
`m(λ)² ≤ 𝟙_outer K_o |V|^{-15/2} + 𝟙_central K_c |U|^{-17/4}`. -/
theorem marginal_sq_le_far {K₁ K₂ : ℝ} (hK₁ : FullPlaneQuadratic (4 / 3) K₁)
    (hK₂ : FullPlaneQuadratic (11 / 8) K₂) :
    ∃ Ko Kc : ℝ, ∀ lam : ℂ × ℂ, 64 ≤ ‖lam‖ →
      marginal lam ^ 2 ≤
        outerRegion.indicator (fun lam => ENNReal.ofReal (Ko * ‖lam.2‖ ^ (-(15 / 2) : ℝ))) lam +
        centralRegion.indicator (fun lam => ENNReal.ofReal (Kc * ‖lam.1‖ ^ (-(17 / 4) : ℝ)))
          lam := by
  obtain ⟨Ko, hKo, hO⟩ := marginal_le_outer
  obtain ⟨Kc, hKc, hC⟩ := marginal_le_central hK₁ hK₂
  refine ⟨Ko ^ 2, Kc ^ 2, fun lam hlam => ?_⟩
  set x := ‖lam.1‖ with hx_def
  set y := ‖lam.2‖ with hy_def
  have hx0 : 0 ≤ x := norm_nonneg _
  have hy0 : 0 ≤ y := norm_nonneg _
  rw [Prod.norm_def] at hlam
  by_cases hout : 16 ≤ y ∧ 256 * x ^ 2 ≤ y ^ 3
  · have hmem : lam ∈ outerRegion := ⟨hout.1, by nlinarith [hout.1, hout.2]⟩
    rw [indicator_of_mem hmem]
    refine le_add_right ?_
    calc marginal lam ^ 2 ≤ ENNReal.ofReal (Ko * y ^ (-(15 / 4) : ℝ)) ^ 2 :=
          pow_le_pow_left₀ bot_le (hO lam hout.1 hout.2) 2
      _ = _ := by
          rw [← ENNReal.ofReal_pow (by positivity), sq_mul_rpow hy0]; norm_num; rfl
  · have hcen : 1 ≤ x ∧ y ≤ 16 * x := by
      rcases lt_or_ge y 16 with hy16 | hy16
      · have hx64 : 64 ≤ x := by
          rcases le_total x y with h | h
          · rw [max_eq_right h] at hlam; linarith
          · rwa [max_eq_left h] at hlam
        constructor <;> linarith
      · have h3 : y ^ 3 < 256 * x ^ 2 := by
          by_contra h; exact hout ⟨hy16, not_lt.mp h⟩
        have hx4 : 4 < x := by nlinarith [pow_le_pow_left₀ (by norm_num) hy16 3]
        refine ⟨by linarith, ?_⟩
        by_contra h
        push Not at h
        nlinarith [mul_lt_mul_of_pos_left h (by positivity : (0 : ℝ) < y ^ 2),
          mul_lt_mul_of_pos_left h (by positivity : (0 : ℝ) < 16 * x * y)]
    have hmem : lam ∈ centralRegion := hcen
    rw [indicator_of_mem hmem]
    refine le_add_left ?_
    calc marginal lam ^ 2 ≤ ENNReal.ofReal (Kc * x ^ (-(17 / 8) : ℝ)) ^ 2 :=
          pow_le_pow_left₀ bot_le (hC lam hcen.1 hcen.2) 2
      _ = _ := by
          rw [← ENNReal.ofReal_pow (by positivity), sq_mul_rpow hx0]; norm_num; rfl

/-- The outer square integral: `∫_outer K |V|^{-15/2} ≤ ∫_{|V| > 8} K π |V|^{-7/2} < ∞`. -/
theorem lintegral_outerRegion_lt_top (K : ℝ) :
    ∫⁻ lam, outerRegion.indicator (fun lam => ENNReal.ofReal (K * ‖lam.2‖ ^ (-(15 / 2) : ℝ)))
      lam < ∞ := by
  have hm : Measurable (outerRegion.indicator
      fun lam : ℂ × ℂ => ENNReal.ofReal (K * ‖lam.2‖ ^ (-(15 / 2) : ℝ))) :=
    (by fun_prop : Measurable fun lam : ℂ × ℂ => ENNReal.ofReal (K * ‖lam.2‖ ^ (-(15 / 2) : ℝ))
      ).indicator measurableSet_outerRegion
  have hS : MeasurableSet {V : ℂ | 8 < ‖V‖} := measurableSet_lt measurable_const measurable_norm
  have hpt : ∀ V : ℂ, ∫⁻ U, outerRegion.indicator
      (fun lam => ENNReal.ofReal (K * ‖lam.2‖ ^ (-(15 / 2) : ℝ))) (U, V) ≤
      {V : ℂ | 8 < ‖V‖}.indicator (fun V => ENNReal.ofReal (K * π) * ‖V‖ₑ⁻¹ ^ (7 / 2 : ℝ)) V := by
    intro V
    by_cases hV : 16 ≤ ‖V‖
    · have hV0 : V ≠ 0 := norm_pos_iff.mp (by linarith)
      have hy0 : 0 < ‖V‖ := by linarith
      have e : ∀ U : ℂ, outerRegion.indicator
          (fun lam => ENNReal.ofReal (K * ‖lam.2‖ ^ (-(15 / 2) : ℝ))) (U, V) =
          (closedBall (0 : ℂ) (‖V‖ ^ 2)).indicator
            (fun _ => ENNReal.ofReal (K * ‖V‖ ^ (-(15 / 2) : ℝ))) U := by
        intro U
        by_cases hU : ‖U‖ ≤ ‖V‖ ^ 2
        · rw [indicator_of_mem (show (U, V) ∈ outerRegion from ⟨hV, hU⟩),
            indicator_of_mem (mem_closedBall_zero_iff.mpr hU)]
        · rw [indicator_of_notMem (show (U, V) ∉ outerRegion from fun h => hU h.2),
            indicator_of_notMem (fun h => hU (mem_closedBall_zero_iff.mp h))]
      rw [lintegral_congr e, lintegral_indicator_const measurableSet_closedBall,
        volume_closedBall_complex (by positivity), indicator_of_mem (by
          change 8 < ‖V‖; linarith : V ∈ {V : ℂ | 8 < ‖V‖}),
        enorm_inv_rpow_of_ne_zero hV0]
      rcases le_total 0 K with hK | hK
      · rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        rw [← Real.rpow_natCast (‖V‖ ^ 2), ← Real.rpow_natCast ‖V‖, ← Real.rpow_mul hy0.le]
        have : ‖V‖ ^ (-(15 / 2) : ℝ) * ‖V‖ ^ (((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ)) =
            ‖V‖ ^ (-(7 / 2) : ℝ) := by rw [← Real.rpow_add hy0]; norm_num
        linear_combination (K * π) * this
      · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hK (by positivity)),
          zero_mul]; exact bot_le
    · have e : ∀ U : ℂ, outerRegion.indicator
          (fun lam => ENNReal.ofReal (K * ‖lam.2‖ ^ (-(15 / 2) : ℝ))) (U, V) = 0 :=
        fun U => indicator_of_notMem (fun h => hV h.1) _
      rw [lintegral_congr e, lintegral_zero]; exact bot_le
  rw [Measure.volume_eq_prod, lintegral_prod_symm _ hm.aemeasurable]
  calc ∫⁻ V, ∫⁻ U, outerRegion.indicator
        (fun lam => ENNReal.ofReal (K * ‖lam.2‖ ^ (-(15 / 2) : ℝ))) (U, V)
      ≤ ∫⁻ V, {V : ℂ | 8 < ‖V‖}.indicator
          (fun V => ENNReal.ofReal (K * π) * ‖V‖ₑ⁻¹ ^ (7 / 2 : ℝ)) V := lintegral_mono hpt
    _ = ENNReal.ofReal (K * π) * ∫⁻ V in {V : ℂ | 8 < ‖V‖}, ‖V‖ₑ⁻¹ ^ (7 / 2 : ℝ) := by
        rw [lintegral_indicator hS, lintegral_const_mul _ (by fun_prop)]
    _ < ∞ := by
        rw [lintegral_norm_gt_inv_rpow (by norm_num) (by norm_num)]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- The central square integral: `∫_central K |U|^{-17/4} ≤ ∫_{|U| > 1/2} 256 π K |U|^{-9/4}`. -/
theorem lintegral_centralRegion_lt_top (K : ℝ) :
    ∫⁻ lam, centralRegion.indicator
      (fun lam => ENNReal.ofReal (K * ‖lam.1‖ ^ (-(17 / 4) : ℝ))) lam < ∞ := by
  have hm : Measurable (centralRegion.indicator
      fun lam : ℂ × ℂ => ENNReal.ofReal (K * ‖lam.1‖ ^ (-(17 / 4) : ℝ))) :=
    (by fun_prop : Measurable fun lam : ℂ × ℂ => ENNReal.ofReal (K * ‖lam.1‖ ^ (-(17 / 4) : ℝ))
      ).indicator measurableSet_centralRegion
  have hS : MeasurableSet {U : ℂ | 1 / 2 < ‖U‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hpt : ∀ U : ℂ, ∫⁻ V, centralRegion.indicator
      (fun lam => ENNReal.ofReal (K * ‖lam.1‖ ^ (-(17 / 4) : ℝ))) (U, V) ≤
      {U : ℂ | 1 / 2 < ‖U‖}.indicator
        (fun U => ENNReal.ofReal (256 * π * K) * ‖U‖ₑ⁻¹ ^ (9 / 4 : ℝ)) U := by
    intro U
    by_cases hU : 1 ≤ ‖U‖
    · have hU0 : U ≠ 0 := norm_pos_iff.mp (by linarith)
      have hx0 : 0 < ‖U‖ := by linarith
      have e : ∀ V : ℂ, centralRegion.indicator
          (fun lam => ENNReal.ofReal (K * ‖lam.1‖ ^ (-(17 / 4) : ℝ))) (U, V) =
          (closedBall (0 : ℂ) (16 * ‖U‖)).indicator
            (fun _ => ENNReal.ofReal (K * ‖U‖ ^ (-(17 / 4) : ℝ))) V := by
        intro V
        by_cases hV : ‖V‖ ≤ 16 * ‖U‖
        · rw [indicator_of_mem (show (U, V) ∈ centralRegion from ⟨hU, hV⟩),
            indicator_of_mem (mem_closedBall_zero_iff.mpr hV)]
        · rw [indicator_of_notMem (show (U, V) ∉ centralRegion from fun h => hV h.2),
            indicator_of_notMem (fun h => hV (mem_closedBall_zero_iff.mp h))]
      rw [lintegral_congr e, lintegral_indicator_const measurableSet_closedBall,
        volume_closedBall_complex (by positivity), indicator_of_mem (by
          change 1 / 2 < ‖U‖; linarith : U ∈ {U : ℂ | 1 / 2 < ‖U‖}),
        enorm_inv_rpow_of_ne_zero hU0]
      rcases le_total 0 K with hK | hK
      · rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        rw [mul_pow, ← Real.rpow_natCast ‖U‖]
        have : ‖U‖ ^ (-(17 / 4) : ℝ) * ‖U‖ ^ ((2 : ℕ) : ℝ) = ‖U‖ ^ (-(9 / 4) : ℝ) := by
          rw [← Real.rpow_add hx0]; norm_num
        linear_combination (256 * π * K) * this
      · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hK (by positivity)),
          zero_mul]; exact bot_le
    · have e : ∀ V : ℂ, centralRegion.indicator
          (fun lam => ENNReal.ofReal (K * ‖lam.1‖ ^ (-(17 / 4) : ℝ))) (U, V) = 0 :=
        fun V => indicator_of_notMem (fun h => hU h.1) _
      rw [lintegral_congr e, lintegral_zero]; exact bot_le
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  calc ∫⁻ U, ∫⁻ V, centralRegion.indicator
        (fun lam => ENNReal.ofReal (K * ‖lam.1‖ ^ (-(17 / 4) : ℝ))) (U, V)
      ≤ ∫⁻ U, {U : ℂ | 1 / 2 < ‖U‖}.indicator
          (fun U => ENNReal.ofReal (256 * π * K) * ‖U‖ₑ⁻¹ ^ (9 / 4 : ℝ)) U := lintegral_mono hpt
    _ = ENNReal.ofReal (256 * π * K) * ∫⁻ U in {U : ℂ | 1 / 2 < ‖U‖}, ‖U‖ₑ⁻¹ ^ (9 / 4 : ℝ) := by
        rw [lintegral_indicator hS, lintegral_const_mul _ (by fun_prop)]
    _ < ∞ := by
        rw [lintegral_norm_gt_inv_rpow (by norm_num) (by norm_num)]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- **The far part is square integrable**: `∫_{‖λ‖ ≥ 64} m² < ∞`. -/
theorem lintegral_marginal_far_sq_lt_top {K₁ K₂ : ℝ} (hK₁ : FullPlaneQuadratic (4 / 3) K₁)
    (hK₂ : FullPlaneQuadratic (11 / 8) K₂) :
    ∫⁻ lam in (ball (0 : ℂ × ℂ) 64)ᶜ, marginal lam ^ 2 < ∞ := by
  obtain ⟨Ko, Kc, h⟩ := marginal_sq_le_far hK₁ hK₂
  have hmo : Measurable (outerRegion.indicator
      fun lam : ℂ × ℂ => ENNReal.ofReal (Ko * ‖lam.2‖ ^ (-(15 / 2) : ℝ))) :=
    (by fun_prop : Measurable fun lam : ℂ × ℂ => ENNReal.ofReal (Ko * ‖lam.2‖ ^ (-(15 / 2) : ℝ))
      ).indicator measurableSet_outerRegion
  have hmc : Measurable (centralRegion.indicator
      fun lam : ℂ × ℂ => ENNReal.ofReal (Kc * ‖lam.1‖ ^ (-(17 / 4) : ℝ))) :=
    (by fun_prop : Measurable fun lam : ℂ × ℂ => ENNReal.ofReal (Kc * ‖lam.1‖ ^ (-(17 / 4) : ℝ))
      ).indicator measurableSet_centralRegion
  calc ∫⁻ lam in (ball (0 : ℂ × ℂ) 64)ᶜ, marginal lam ^ 2
      ≤ ∫⁻ lam in (ball (0 : ℂ × ℂ) 64)ᶜ,
          (outerRegion.indicator (fun lam => ENNReal.ofReal (Ko * ‖lam.2‖ ^ (-(15 / 2) : ℝ))) lam +
          centralRegion.indicator (fun lam => ENNReal.ofReal (Kc * ‖lam.1‖ ^ (-(17 / 4) : ℝ)))
            lam) :=
        setLIntegral_mono (hmo.add hmc) fun lam hl =>
          h lam (not_lt.mp (fun h' => hl (mem_ball_zero_iff.mpr h')))
    _ ≤ ∫⁻ lam, (outerRegion.indicator
          (fun lam => ENNReal.ofReal (Ko * ‖lam.2‖ ^ (-(15 / 2) : ℝ))) lam +
          centralRegion.indicator (fun lam => ENNReal.ofReal (Kc * ‖lam.1‖ ^ (-(17 / 4) : ℝ)))
            lam) := setLIntegral_le_lintegral _ _
    _ < ∞ := by
        rw [lintegral_add_left hmo]
        exact ENNReal.add_lt_top.mpr
          ⟨lintegral_outerRegion_lt_top Ko, lintegral_centralRegion_lt_top Kc⟩

end SLT.MiddlePositions.Three
