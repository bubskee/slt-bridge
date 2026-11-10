/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Downstream.Radial
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Inverse powers of a quadratic on a disc

The note's Lemma 1 integrates `|𝔇|^{-1-α}` in `P₃`, where `𝔇` is a quadratic in `P₃`. This file
gives the two estimates it needs, **for every radius** (the note derives them only for small `ε`):

* `lintegral_ball_inv_quadratic_le` (two roots, `A ≠ 0`): with `b = 2α + η`,
  `∫_{|z| < R} |A z² + B z + C|^{-1-α} ≤ c R^η |A|^{b-1-α} |B² - 4AC|^{-b/2}`.
  This is the note's root-separation bound `δ^{-2α}` (and `1 + log(ε/δ)` at `α = 0`), with the
  logarithm traded for an arbitrarily small power `η`;
* `lintegral_ball_one_inv_quadratic_le` (one dominant root, `8|A| ≤ |B|`, `A` possibly `0`):
  `∫_{|z| < 1} |A z² + B z + C|^{-a} ≤ (|B|/4)^{-a} (2π/(2-a) + π)`.
  This covers the note's outer region and the directions near `P₀ = 0`, where the leading
  coefficient degenerates but `B` (the note's `∂𝔇/∂P₃ = 4P₁³`) is a unit.
-/

@[expose] public section

namespace SLT.PositionFour.Downstream

open MeasureTheory Set Real Metric
open scoped ENNReal NNReal

/-! ### Real forms of inverse powers -/

/-- For `x ≠ 0`, `|x|^{-t}` in `ℝ≥0∞` is the real power. -/
theorem enorm_inv_rpow_of_ne_zero {x : ℂ} (hx : x ≠ 0) (t : ℝ) :
    ‖x‖ₑ⁻¹ ^ t = ENNReal.ofReal (‖x‖ ^ (-t)) := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [← ofReal_norm, ← ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_rpow_of_pos
    (inv_pos.mpr hpos), Real.inv_rpow hpos.le, Real.rpow_neg hpos.le]

/-- For `r > 0`, `r^{-t}` in `ℝ≥0∞` is the real power. -/
theorem ofReal_inv_rpow_of_pos {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (ENNReal.ofReal r)⁻¹ ^ t = ENNReal.ofReal (r ^ (-t)) := by
  rw [← ENNReal.ofReal_inv_of_pos hr, ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hr),
    Real.inv_rpow hr.le, Real.rpow_neg hr.le]

/-- The inverse power of a product, `|a x|^{-t} = |a|^{-t} |x|^{-t}`, for `a ≠ 0` and `t ≥ 0`. -/
theorem enorm_mul_inv_rpow {a : ℂ} (ha : a ≠ 0) (x : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖a * x‖ₑ⁻¹ ^ t = ENNReal.ofReal (‖a‖ ^ (-t)) * ‖x‖ₑ⁻¹ ^ t := by
  rw [enorm_mul, ENNReal.mul_inv (Or.inr enorm_ne_top) (Or.inl enorm_ne_top),
    ENNReal.mul_rpow_of_nonneg _ _ ht, enorm_inv_rpow_of_ne_zero ha]

/-- The inverse power of a power, `|x^n|^{-t} = |x|^{-n t}`. -/
theorem enorm_pow_inv_rpow (x : ℂ) (n : ℕ) (t : ℝ) :
    ‖x ^ n‖ₑ⁻¹ ^ t = ‖x‖ₑ⁻¹ ^ ((n : ℝ) * t) := by
  rw [enorm_pow, ENNReal.inv_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]

/-- A positive weight cancels part of an inverse power: `|x|^u |x|^{-(u+v)} ≤ |x|^{-v}` for
`u ≥ 0` (both sides are `∞`, or the left side is `0`, at `x = 0`). -/
theorem ofReal_rpow_mul_inv_rpow_le (x : ℂ) {u v : ℝ} (hu : 0 ≤ u) :
    ENNReal.ofReal (‖x‖ ^ u) * ‖x‖ₑ⁻¹ ^ (u + v) ≤ ‖x‖ₑ⁻¹ ^ v := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases hu.lt_or_eq with hu | rfl
    · simp [Real.zero_rpow hu.ne']
    · simp
  · rw [enorm_inv_rpow_of_ne_zero hx, enorm_inv_rpow_of_ne_zero hx,
      ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (norm_pos_iff.mpr hx)]
    exact le_of_eq (by ring_nf)

/-! ### Two roots -/

/-- The pointwise split of `|(z - r₁)(z - r₂)|^{-1-α}` into two single poles: with `d₁, d₂` the
distances to the roots and `δ ≤ d₁ + d₂` their separation,
`(d₁ d₂)^{-1-α} ≤ (δ/2)^{-(2α+η)} (d₁^{-(2-η)} + d₂^{-(2-η)})`. -/
private lemma inv_mul_rpow_le_aux {d₁ d₂ δ : ℝ≥0∞} (h1 : d₁ ≠ ⊤) (h2 : d₂ ≠ ⊤)
    (hδ : δ ≤ d₁ + d₂) (h12 : d₁ ≤ d₂) {α η : ℝ} (hα : 0 ≤ α) (hη : 0 ≤ η) (hαη : α + η ≤ 1) :
    (d₁ * d₂)⁻¹ ^ (1 + α) ≤ (δ / 2)⁻¹ ^ (2 * α + η) * d₁⁻¹ ^ (2 - η) := by
  have hδ2 : δ / 2 ≤ d₂ := by
    rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
    calc δ ≤ d₁ + d₂ := hδ
      _ ≤ d₂ + d₂ := add_le_add_left h12 _
      _ = d₂ * 2 := by rw [mul_two]
  have e2 : d₂⁻¹ ^ (1 + α) ≤ d₁⁻¹ ^ (1 - α - η) * (δ / 2)⁻¹ ^ (2 * α + η) := by
    rw [show 1 + α = (1 - α - η) + (2 * α + η) by ring,
      ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by linarith)]
    exact mul_le_mul' (ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.mpr h12) (by linarith))
      (ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.mpr hδ2) (by linarith))
  have e1 : d₁⁻¹ ^ (1 + α) * d₁⁻¹ ^ (1 - α - η) = d₁⁻¹ ^ (2 - η) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by linarith)]; ring_nf
  rw [ENNReal.mul_inv (Or.inr h2) (Or.inl h1), ENNReal.mul_rpow_of_nonneg _ _ (by linarith)]
  calc d₁⁻¹ ^ (1 + α) * d₂⁻¹ ^ (1 + α)
      ≤ d₁⁻¹ ^ (1 + α) * (d₁⁻¹ ^ (1 - α - η) * (δ / 2)⁻¹ ^ (2 * α + η)) := by gcongr
    _ = (δ / 2)⁻¹ ^ (2 * α + η) * d₁⁻¹ ^ (2 - η) := by rw [← mul_assoc, e1, mul_comm]

/-- **Two poles on a disc**: for `0 ≤ α`, `0 < η`, `α + η ≤ 1`,
`∫_{|z| < R} |(z - r₁)(z - r₂)|^{-1-α} ≤ 2 (2π/η + π) R^η (|r₁ - r₂|/2)^{-(2α+η)}`. -/
theorem lintegral_ball_inv_mul_rpow_le (r₁ r₂ : ℂ) {α η R : ℝ} (hα : 0 ≤ α) (hη : 0 < η)
    (hαη : α + η ≤ 1) (hR : 0 < R) :
    ∫⁻ z in ball (0 : ℂ) R, ‖(z - r₁) * (z - r₂)‖ₑ⁻¹ ^ (1 + α) ≤
      (‖r₁ - r₂‖ₑ / 2)⁻¹ ^ (2 * α + η) * (2 * ENNReal.ofReal ((2 * π / η + π) * R ^ η)) := by
  set c := (‖r₁ - r₂‖ₑ / 2)⁻¹ ^ (2 * α + η)
  have hpt : ∀ z : ℂ, ‖(z - r₁) * (z - r₂)‖ₑ⁻¹ ^ (1 + α) ≤
      c * (‖z - r₁‖ₑ⁻¹ ^ (2 - η) + ‖z - r₂‖ₑ⁻¹ ^ (2 - η)) := by
    intro z
    have hδ : ‖r₁ - r₂‖ₑ ≤ ‖z - r₁‖ₑ + ‖z - r₂‖ₑ := by
      have : r₁ - r₂ = (z - r₂) - (z - r₁) := by ring
      rw [this, add_comm]; exact enorm_sub_le
    rw [enorm_mul, mul_add]
    rcases le_total ‖z - r₁‖ₑ ‖z - r₂‖ₑ with h | h
    · exact (inv_mul_rpow_le_aux enorm_ne_top enorm_ne_top hδ h hα hη.le hαη).trans le_self_add
    · rw [mul_comm]
      exact (inv_mul_rpow_le_aux enorm_ne_top enorm_ne_top (by rwa [add_comm]) h hα hη.le
        hαη).trans le_add_self
  have hm : ∀ r : ℂ, Measurable fun z : ℂ => ‖z - r‖ₑ⁻¹ ^ (2 - η) := fun r => by fun_prop
  have hs0 : 0 ≤ 2 - η := by linarith
  have hball : ∀ r : ℂ, ∫⁻ z in ball (0 : ℂ) R, ‖z - r‖ₑ⁻¹ ^ (2 - η) ≤
      ENNReal.ofReal ((2 * π / η + π) * R ^ η) := by
    intro r
    have := lintegral_ball_sub_inv_rpow_le r hs0 (by linarith : 2 - η < 2) hR
    simpa [show (2 : ℝ) - (2 - η) = η by ring] using this
  calc ∫⁻ z in ball (0 : ℂ) R, ‖(z - r₁) * (z - r₂)‖ₑ⁻¹ ^ (1 + α)
      ≤ ∫⁻ z in ball (0 : ℂ) R, c * (‖z - r₁‖ₑ⁻¹ ^ (2 - η) + ‖z - r₂‖ₑ⁻¹ ^ (2 - η)) :=
        lintegral_mono hpt
    _ = c * ((∫⁻ z in ball (0 : ℂ) R, ‖z - r₁‖ₑ⁻¹ ^ (2 - η)) +
          ∫⁻ z in ball (0 : ℂ) R, ‖z - r₂‖ₑ⁻¹ ^ (2 - η)) := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_add_left (hm r₁)]
    _ ≤ c * (2 * ENNReal.ofReal ((2 * π / η + π) * R ^ η)) := by
        rw [two_mul]; gcongr <;> exact hball _

/-- **Factorisation of a quadratic** with `A ≠ 0`: there are roots `r₁, r₂` with
`A z² + B z + C = A (z - r₁)(z - r₂)` and `(A (r₁ - r₂))² = B² - 4AC`. -/
theorem exists_quadratic_factor {A B C : ℂ} (hA : A ≠ 0) :
    ∃ r₁ r₂ : ℂ, (∀ z, A * z ^ 2 + B * z + C = A * ((z - r₁) * (z - r₂))) ∧
      (A * (r₁ - r₂)) ^ 2 = B ^ 2 - 4 * A * C := by
  obtain ⟨S, hS⟩ := IsAlgClosed.exists_pow_nat_eq (B ^ 2 - 4 * A * C) two_pos
  refine ⟨(-B + S) / (2 * A), (-B - S) / (2 * A), fun z => ?_, ?_⟩
  · field_simp
    linear_combination hS
  · field_simp
    linear_combination 4 * hS

/-- The exponent bookkeeping of `lintegral_ball_inv_quadratic_le`, with `Y = |r₁ - r₂|` and
`|B² - 4AC| = (|A| Y)²`. -/
private lemma key_identity {a Y K b α : ℝ} (ha : 0 < a) (hY : 0 < Y) :
    a ^ (-(1 + α)) * ((Y / 2) ^ (-b) * (2 * K)) =
      2 ^ (b + 1) * K * a ^ (b - 1 - α) * ((a * Y) ^ 2) ^ (-(b / 2)) := by
  rw [show ((a * Y) ^ 2 : ℝ) = (a * Y) ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul (by positivity),
    show (2 : ℝ) * (-(b / 2)) = -b by ring, Real.mul_rpow ha.le hY.le,
    Real.div_rpow hY.le (by norm_num), show b - 1 - α = b + -(1 + α) by ring, Real.rpow_add ha,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, Real.rpow_neg ha.le b,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) b]
  have h1 : 0 < a ^ b := Real.rpow_pos_of_pos ha b
  have h2 : 0 < (2 : ℝ) ^ b := Real.rpow_pos_of_pos (by norm_num) b
  field_simp

/-- **Two roots, in terms of the discriminant**: for `A ≠ 0`, `0 ≤ α`, `0 < η`, `α + η ≤ 1`, and
`b = 2α + η`,
`∫_{|z| < R} |A z² + B z + C|^{-1-α} ≤ 2^{b+1} (2π/η + π) R^η |A|^{b-1-α} |B² - 4AC|^{-b/2}`. -/
theorem lintegral_ball_inv_quadratic_le {A B C : ℂ} (hA : A ≠ 0) {α η R : ℝ} (hα : 0 ≤ α)
    (hη : 0 < η) (hαη : α + η ≤ 1) (hR : 0 < R) :
    ∫⁻ z in ball (0 : ℂ) R, ‖A * z ^ 2 + B * z + C‖ₑ⁻¹ ^ (1 + α) ≤
      ENNReal.ofReal (2 ^ (2 * α + η + 1) * ((2 * π / η + π) * R ^ η) *
        ‖A‖ ^ (2 * α + η - 1 - α)) * ‖B ^ 2 - 4 * A * C‖ₑ⁻¹ ^ ((2 * α + η) / 2) := by
  obtain ⟨r₁, r₂, hfac, hdisc⟩ := exists_quadratic_factor (B := B) (C := C) hA
  set b := 2 * α + η with hb
  set K := (2 * π / η + π) * R ^ η with hK
  have hKpos : 0 < K := by positivity
  have hb0 : 0 < b := by positivity
  simp_rw [hfac]
  have hsplit : ∀ z : ℂ, ‖A * ((z - r₁) * (z - r₂))‖ₑ⁻¹ ^ (1 + α) =
      ENNReal.ofReal (‖A‖ ^ (-(1 + α))) * ‖(z - r₁) * (z - r₂)‖ₑ⁻¹ ^ (1 + α) :=
    fun z => enorm_mul_inv_rpow hA _ (by linarith)
  simp_rw [hsplit]
  rw [lintegral_const_mul _ (by fun_prop)]
  have hQ := lintegral_ball_inv_mul_rpow_le r₁ r₂ hα hη hαη hR
  refine (mul_le_mul_right hQ _).trans ?_
  rcases eq_or_ne (B ^ 2 - 4 * A * C) 0 with hD | hD
  · -- double root: the right side is `∞`
    rw [hD, enorm_zero, ENNReal.inv_zero, ENNReal.top_rpow_of_pos (by positivity),
      ENNReal.mul_top (by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        have : 0 < ‖A‖ := norm_pos_iff.mpr hA
        positivity)]
    exact le_top
  · have hr : r₁ - r₂ ≠ 0 := by
      intro h; apply hD; rw [← hdisc, h, mul_zero]; ring
    have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA
    have hrpos : 0 < ‖r₁ - r₂‖ := norm_pos_iff.mpr hr
    have hnorm : ‖B ^ 2 - 4 * A * C‖ = (‖A‖ * ‖r₁ - r₂‖) ^ 2 := by
      rw [← norm_mul, ← norm_pow, hdisc]
    rw [enorm_inv_rpow_of_ne_zero hD,
      show ‖r₁ - r₂‖ₑ / 2 = ENNReal.ofReal (‖r₁ - r₂‖ / 2) by
        rw [ENNReal.ofReal_div_of_pos two_pos, ofReal_norm, ENNReal.ofReal_ofNat],
      ofReal_inv_rpow_of_pos (by positivity), ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hnorm]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (key_identity hApos hrpos))

/-! ### One dominant root -/

/-- If `8|A| ≤ |B|` and `B ≠ 0`, then on the unit disc the quadratic is bounded below by
`|B|/4` times the distance to one of its roots. -/
theorem exists_root_lower_bound {A B C : ℂ} (hB : B ≠ 0) (hAB : 8 * ‖A‖ ≤ ‖B‖) :
    ∃ r : ℂ, ∀ z : ℂ, ‖z‖ < 1 → ‖B‖ / 4 * ‖z - r‖ ≤ ‖A * z ^ 2 + B * z + C‖ := by
  rcases eq_or_ne A 0 with rfl | hA
  · refine ⟨-C / B, fun z _ => ?_⟩
    have : 0 * z ^ 2 + B * z + C = B * (z - -C / B) := by field_simp; ring
    rw [this, norm_mul]
    have := norm_nonneg (z - -C / B)
    nlinarith [norm_nonneg B]
  · obtain ⟨r₁, r₂, hfac, -⟩ := exists_quadratic_factor (B := B) (C := C) hA
    have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA
    -- the sum of the roots is `-B/A`
    have hsum : A * (r₁ + r₂) = -B := by
      have h0 := hfac 0
      have h1 := hfac 1
      have : A * 1 ^ 2 + B * 1 + C - (A * 0 ^ 2 + B * 0 + C) =
          A * ((1 - r₁) * (1 - r₂)) - A * ((0 - r₁) * (0 - r₂)) := by rw [h0, h1]
      linear_combination this
    have hB' : ‖B‖ ≤ ‖A‖ * (‖r₁‖ + ‖r₂‖) := by
      rw [← norm_neg B, ← hsum, norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hApos.le
    -- the larger root is far from the unit disc
    have key : ∀ {rl rs : ℂ}, ‖rs‖ ≤ ‖rl‖ → ‖B‖ ≤ ‖A‖ * (‖rl‖ + ‖rs‖) →
        (∀ z, A * z ^ 2 + B * z + C = A * ((z - rl) * (z - rs))) →
        ∀ z : ℂ, ‖z‖ < 1 → ‖B‖ / 4 * ‖z - rs‖ ≤ ‖A * z ^ 2 + B * z + C‖ := by
      intro rl rs hle hBl hf z hz
      rw [hf, norm_mul, norm_mul, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have h1 : ‖rl‖ - ‖z‖ ≤ ‖z - rl‖ := by
        have := norm_sub_norm_le rl z; rw [norm_sub_rev] at this; linarith
      have h2 : ‖B‖ ≤ 2 * ‖A‖ * ‖rl‖ := by nlinarith
      have h3 : 8 * ‖A‖ ≤ 2 * ‖A‖ * ‖rl‖ := hAB.trans h2
      have h4 : 4 ≤ ‖rl‖ := by nlinarith
      nlinarith [norm_nonneg z]
    rcases le_total ‖r₂‖ ‖r₁‖ with h | h
    · exact ⟨r₂, key h hB' hfac⟩
    · refine ⟨r₁, key h (by linarith) fun z => ?_⟩
      rw [hfac z]; ring

/-- **One dominant root on the unit disc**: if `B ≠ 0`, `8|A| ≤ |B|` and `0 ≤ a < 2`, then
`∫_{|z| < 1} |A z² + B z + C|^{-a} ≤ (|B|/4)^{-a} (2π/(2-a) + π)`. -/
theorem lintegral_ball_one_inv_quadratic_le {A B C : ℂ} (hB : B ≠ 0) (hAB : 8 * ‖A‖ ≤ ‖B‖)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 2) :
    ∫⁻ z in ball (0 : ℂ) 1, ‖A * z ^ 2 + B * z + C‖ₑ⁻¹ ^ a ≤
      ENNReal.ofReal ((‖B‖ / 4) ^ (-a) * (2 * π / (2 - a) + π)) := by
  obtain ⟨r, hr⟩ := exists_root_lower_bound (C := C) hB hAB
  have hBpos : 0 < ‖B‖ / 4 := by have := norm_pos_iff.mpr hB; positivity
  have hpt : ∀ z ∈ ball (0 : ℂ) 1, ‖A * z ^ 2 + B * z + C‖ₑ⁻¹ ^ a ≤
      ENNReal.ofReal ((‖B‖ / 4) ^ (-a)) * ‖z - r‖ₑ⁻¹ ^ a := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    rw [← ofReal_inv_rpow_of_pos hBpos, ← ENNReal.mul_rpow_of_nonneg _ _ ha0,
      ← ENNReal.mul_inv (Or.inr enorm_ne_top) (Or.inl ENNReal.ofReal_ne_top)]
    refine ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.mpr ?_) ha0
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hBpos.le]
    exact ENNReal.ofReal_le_ofReal (hr z hz)
  calc ∫⁻ z in ball (0 : ℂ) 1, ‖A * z ^ 2 + B * z + C‖ₑ⁻¹ ^ a
      ≤ ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal ((‖B‖ / 4) ^ (-a)) * ‖z - r‖ₑ⁻¹ ^ a :=
        setLIntegral_mono (by fun_prop) hpt
    _ = ENNReal.ofReal ((‖B‖ / 4) ^ (-a)) * ∫⁻ z in ball (0 : ℂ) 1, ‖z - r‖ₑ⁻¹ ^ a :=
        lintegral_const_mul _ (by fun_prop)
    _ ≤ ENNReal.ofReal ((‖B‖ / 4) ^ (-a)) * ENNReal.ofReal ((2 * π / (2 - a) + π) * 1 ^ (2 - a)) :=
        by gcongr; exact lintegral_ball_sub_inv_rpow_le r ha0 ha one_pos
    _ = ENNReal.ofReal ((‖B‖ / 4) ^ (-a) * (2 * π / (2 - a) + π)) := by
        rw [Real.one_rpow, mul_one, ← ENNReal.ofReal_mul (by positivity)]

end SLT.PositionFour.Downstream
