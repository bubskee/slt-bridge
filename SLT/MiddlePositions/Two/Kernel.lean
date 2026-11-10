/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Two.Planar

/-!
# The two-form suffix kernel at position two

Section 3 of `complex_middle_positions.tex`: Lemma "An explicit two-variable integral" and Lemma
"Weighted two-form suffix". Write a cubic as `P = (z, Q, u, v)` (moment coordinates) and
`h = u² - Q v`. As a quadratic in the free coefficient `z = P₀`,
`𝔇(z, Q, u, v) = v² ((z - c)² - δ)` with `c = u(u² - 3h)/v²` and `δ = 4h³/v⁴` (`disc_coords`).

* `L t z = ∫_{|u| < 1} |u² - z|^{-t}` and `L_le`: `L t z ≤ C |z|^{-s}` for every `z`, when
  `0 ≤ t ≤ 9/8` and `1/8 ≤ s ≤ t`. This replaces the note's case split on `|z| ≤ 2` and its
  Hölder and Cauchy–Schwarz steps by the pointwise bound `x^t ≤ x^{9/8} + 1`.
* `G Q u v` collects the note's five terms `|v|^{-a} |h|^{-t}` left by the full-plane
  `z`-integration (`(a, t) = (4/3, 1), (5/4, 9/8), (7/4, 9/8), (7/4, 7/8), (7/4, 3/4)`, the second
  with the factor `(1 + |Q|)^{1/4}`); the `z`-step itself is `lintegral_F_coords_le` in
  `Suffix.lean`.
* `lintegral_G_le`: the note's `J` bounds, in the form
  `∫∫_{|u|, |v| < 1} G ≤ C (|Q|^{-1/8} + |Q|^{-1/4} + |Q|^{-1/2})`. Each `J_{a,t}(Q)` is bounded by
  `C |Q|^{-s}` for one exponent `s` with `a + s < 2`; no large-`|Q|` decay is needed, since the
  assembly only uses a uniform bound on unit `Q`-discs.
The uniform bound on unit `Q`-discs, `setLIntegral_box_F_le`, is in `Suffix.lean`.
-/

@[expose] public section

namespace SLT.MiddlePositions.Two

open MeasureTheory Set Real Metric SLT.PositionFour SLT.PositionFour.Downstream
open scoped ENNReal NNReal

/-! ### Small facts in `ℝ≥0∞` -/

/-- `|0|^{-s} = ∞` for `s > 0`. -/
theorem enorm_zero_inv_rpow {s : ℝ} (hs : 0 < s) : ‖(0 : ℂ)‖ₑ⁻¹ ^ s = ⊤ := by
  simp [ENNReal.top_rpow_of_pos hs]

/-- `|x|^{-s} ≠ 0`. -/
theorem enorm_inv_rpow_ne_zero (x : ℂ) {s : ℝ} (hs : 0 ≤ s) : ‖x‖ₑ⁻¹ ^ s ≠ 0 :=
  (ENNReal.rpow_pos_of_nonneg (ENNReal.inv_pos.mpr enorm_ne_top) hs).ne'

/-- `|x y|^{-s} = |x|^{-s} |y|^{-s}` for `s ≥ 0`. -/
theorem enorm_mul_inv_rpow' (x y : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    ‖x * y‖ₑ⁻¹ ^ s = ‖x‖ₑ⁻¹ ^ s * ‖y‖ₑ⁻¹ ^ s := by
  rw [enorm_mul, ENNReal.mul_inv (Or.inr enorm_ne_top) (Or.inl enorm_ne_top),
    ENNReal.mul_rpow_of_nonneg _ _ hs]

/-- `(s.indicator 1 x) f(x) = s.indicator f x`. -/
theorem indicator_one_mul_eq {α : Type*} (s : Set α) (f : α → ℝ≥0∞) (x : α) :
    s.indicator 1 x * f x = s.indicator f x := by
  by_cases hx : x ∈ s <;> simp [hx]

/-- An indicator of `1` is finite. -/
theorem indicator_one_ne_top {α : Type*} (s : Set α) (x : α) :
    s.indicator (1 : α → ℝ≥0∞) x ≠ ⊤ := by
  by_cases hx : x ∈ s <;> simp [hx]

/-- The volume of the unit disc is `π`. -/
theorem volume_ball_one : volume (ball (0 : ℂ) 1) = ENNReal.ofReal π := by
  rw [Complex.volume_ball, ENNReal.ofReal_one, one_pow, one_mul, ← ENNReal.ofReal_coe_nnreal,
    NNReal.coe_real_pi]

/-! ### The disc integral `L` -/

/-- `L_t(z) = ∫_{|u| < 1} |u² - z|^{-t}`. -/
noncomputable def L (t : ℝ) (z : ℂ) : ℝ≥0∞ := ∫⁻ u in ball (0 : ℂ) 1, ‖u ^ 2 - z‖ₑ⁻¹ ^ t

/-- The constant of `L_le`. -/
noncomputable def Lc (K : ℝ) : ℝ := 2 * K + 4 * π

/-- `Lc K > 0` for `K ≥ 0`. -/
theorem Lc_pos {K : ℝ} (hK0 : 0 ≤ K) : 0 < Lc K := by unfold Lc; positivity

/-- **The disc integral of a quadratic singularity** (the note's `L_t`): for `0 ≤ t ≤ 9/8` and
`1/8 ≤ s ≤ t`, `∫_{|u| < 1} |u² - z|^{-t} ≤ (2K + 4π) |z|^{-s}` for every `z`, where `K` is the
constant of `FullPlaneQuadratic (9/8)`. -/
theorem L_le {K t s : ℝ} (hK : FullPlaneQuadratic (9 / 8) K) (hK0 : 0 ≤ K) (ht0 : 0 ≤ t)
    (ht : t ≤ 9 / 8) (hs : 1 / 8 ≤ s) (hst : s ≤ t) (z : ℂ) :
    L t z ≤ ENNReal.ofReal (Lc K) * ‖z‖ₑ⁻¹ ^ s := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [enorm_zero_inv_rpow (by linarith),
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Lc_pos hK0)).ne']
    exact le_top
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [enorm_inv_rpow_of_ne_zero hz, ← ENNReal.ofReal_mul (Lc_pos hK0).le]
  have h2t : (2 : ℝ) ^ t ≤ 4 :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith : t ≤ 2)).trans_eq (by norm_num)
  have hzs : 0 ≤ ‖z‖ ^ (-s) := by positivity
  by_cases hz2 : 2 ≤ ‖z‖
  · -- far from the disc: `|u² - z| ≥ |z|/2`
    have hpt : ∀ u ∈ ball (0 : ℂ) 1,
        ‖u ^ 2 - z‖ₑ⁻¹ ^ t ≤ ENNReal.ofReal (2 ^ t * ‖z‖ ^ (-s)) := by
      intro u hu
      rw [mem_ball_zero_iff] at hu
      have h1 : ‖z‖ / 2 ≤ ‖u ^ 2 - z‖ := by
        have := norm_sub_norm_le z (u ^ 2)
        rw [norm_sub_rev z, norm_pow] at this
        nlinarith [norm_nonneg u]
      have hne : u ^ 2 - z ≠ 0 := norm_pos_iff.mp (by linarith)
      rw [enorm_inv_rpow_of_ne_zero hne]
      refine ENNReal.ofReal_le_ofReal ?_
      calc ‖u ^ 2 - z‖ ^ (-t) ≤ (‖z‖ / 2) ^ (-t) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
        _ = 2 ^ t * ‖z‖ ^ (-t) := by
            rw [Real.div_rpow hz'.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
              div_inv_eq_mul, mul_comm]
        _ ≤ 2 ^ t * ‖z‖ ^ (-s) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) (by positivity)
    calc L t z ≤ ∫⁻ _ in ball (0 : ℂ) 1, ENNReal.ofReal (2 ^ t * ‖z‖ ^ (-s)) :=
          setLIntegral_mono measurable_const hpt
      _ = ENNReal.ofReal (2 ^ t * ‖z‖ ^ (-s) * π) := by
          rw [setLIntegral_const, volume_ball_one, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          unfold Lc
          nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right h2t (mul_nonneg hzs Real.pi_pos.le)]
  · -- near the disc: `x^t ≤ x^{9/8} + 1`, then the full-plane bound
    rw [not_le] at hz2
    have hpt : ∀ u : ℂ, ‖u ^ 2 - z‖ₑ⁻¹ ^ t ≤ ‖u ^ 2 - z‖ₑ⁻¹ ^ (9 / 8 : ℝ) + 1 := by
      intro u
      rcases le_total (‖u ^ 2 - z‖ₑ⁻¹) 1 with h | h
      · exact (ENNReal.rpow_le_one h ht0).trans le_add_self
      · exact (ENNReal.rpow_le_rpow_of_exponent_le h ht).trans le_self_add
    have hfull : ∫⁻ u, ‖u ^ 2 - z‖ₑ⁻¹ ^ (9 / 8 : ℝ) ≤
        ENNReal.ofReal (K * (4 * ‖z‖) ^ (-(9 / 8 - 1 : ℝ))) := by
      have e : ∀ u : ℂ, u ^ 2 - z = 1 * u ^ 2 + 0 * u + -z := fun u => by ring
      simp_rw [e]
      refine (hK 1 0 (-z) one_ne_zero).trans (le_of_eq ?_)
      have hd : (0 : ℂ) ^ 2 - 4 * 1 * -z = 4 * z := by ring
      rw [hd, enorm_inv_rpow_of_ne_zero (by simp [hz]), norm_one, Real.one_rpow, mul_one,
        ← ENNReal.ofReal_mul hK0, norm_mul, Complex.norm_ofNat]
    have r1 : (4 * ‖z‖) ^ (-(9 / 8 - 1 : ℝ)) ≤ ‖z‖ ^ (-(1 / 8 : ℝ)) :=
      (Real.rpow_le_rpow_of_nonpos hz' (by linarith) (by norm_num)).trans_eq (by norm_num)
    have r2 : ‖z‖ ^ (-(1 / 8 : ℝ)) = ‖z‖ ^ (-s) * ‖z‖ ^ (s - 1 / 8) :=
      (rpow_mul_rpow_eq hz' (by ring)).symm
    have r3 : ‖z‖ ^ (s - 1 / 8) ≤ 2 :=
      (Real.rpow_le_rpow hz'.le hz2.le (by linarith)).trans
        ((Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith : s - 1 / 8 ≤ 1)).trans_eq
          (Real.rpow_one 2))
    have r4 : 1 = ‖z‖ ^ (-s) * ‖z‖ ^ s := by
      rw [rpow_mul_rpow_eq hz' (by ring : -s + s = 0), Real.rpow_zero]
    have r5 : ‖z‖ ^ s ≤ 4 :=
      (Real.rpow_le_rpow hz'.le hz2.le (by linarith)).trans
        ((Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith : s ≤ 2)).trans_eq
          (by norm_num))
    calc L t z ≤ ∫⁻ u in ball (0 : ℂ) 1, (‖u ^ 2 - z‖ₑ⁻¹ ^ (9 / 8 : ℝ) + 1) :=
          lintegral_mono fun u => hpt u
      _ = (∫⁻ u in ball (0 : ℂ) 1, ‖u ^ 2 - z‖ₑ⁻¹ ^ (9 / 8 : ℝ)) + ENNReal.ofReal π := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, one_mul,
            volume_ball_one]
      _ ≤ ENNReal.ofReal (K * (4 * ‖z‖) ^ (-(9 / 8 - 1 : ℝ))) + ENNReal.ofReal π := by
          gcongr
          exact (setLIntegral_le_lintegral _ _).trans hfull
      _ ≤ _ := by
          rw [← ENNReal.ofReal_add (by positivity) Real.pi_pos.le]
          refine ENNReal.ofReal_le_ofReal ?_
          unfold Lc
          have hzs' : 0 ≤ ‖z‖ ^ (-s) := hzs
          nlinarith [mul_le_mul_of_nonneg_left r1 hK0, mul_le_mul_of_nonneg_left r3 hzs',
            mul_le_mul_of_nonneg_left r5 hzs', Real.pi_pos]

/-- One of the note's `J` terms, pointwise in `v`: for `|v| < 1`, `a ≥ 0` and `a + s ≤ 15/8`,
`|v|^{-a} L_t(Q v) ≤ C |Q|^{-s} |v|^{-15/8}`. -/
theorem rpow_mul_L_le {K t s a : ℝ} (hK : FullPlaneQuadratic (9 / 8) K) (hK0 : 0 ≤ K)
    (ht0 : 0 ≤ t) (ht : t ≤ 9 / 8) (hs : 1 / 8 ≤ s) (hst : s ≤ t) (ha : 0 ≤ a)
    (has : a + s ≤ 15 / 8) (Q : ℂ) {v : ℂ} (hv : ‖v‖ < 1) :
    ‖v‖ₑ⁻¹ ^ a * L t (Q * v) ≤
      ENNReal.ofReal (Lc K) * ‖Q‖ₑ⁻¹ ^ s * ‖v‖ₑ⁻¹ ^ (15 / 8 : ℝ) := by
  have hv1 : 1 ≤ ‖v‖ₑ⁻¹ := ENNReal.one_le_inv.mpr (by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_one.mpr hv.le)
  calc ‖v‖ₑ⁻¹ ^ a * L t (Q * v)
      ≤ ‖v‖ₑ⁻¹ ^ a * (ENNReal.ofReal (Lc K) * (‖Q‖ₑ⁻¹ ^ s * ‖v‖ₑ⁻¹ ^ s)) := by
        gcongr
        exact (L_le hK hK0 ht0 ht hs hst _).trans_eq
          (by rw [enorm_mul_inv_rpow' _ _ (by linarith)])
    _ = ENNReal.ofReal (Lc K) * ‖Q‖ₑ⁻¹ ^ s * ‖v‖ₑ⁻¹ ^ (a + s) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ ha (by linarith)]; ring
    _ ≤ _ := by
        gcongr

/-! ### The integrand after the `z`-integration -/

/-- The five terms left by the full-plane `z`-integration (the note's proof of Lemma
"Weighted two-form suffix"), with `h = u² - Q v`. -/
noncomputable def G (Q u v : ℂ) : ℝ≥0∞ :=
  ‖v‖ₑ⁻¹ ^ (4 / 3 : ℝ) * ‖u ^ 2 - Q * v‖ₑ⁻¹ ^ (1 : ℝ) +
    ENNReal.ofReal ((1 + ‖Q‖) ^ (1 / 4 : ℝ)) *
      (‖v‖ₑ⁻¹ ^ (5 / 4 : ℝ) * ‖u ^ 2 - Q * v‖ₑ⁻¹ ^ (9 / 8 : ℝ)) +
    ‖v‖ₑ⁻¹ ^ (7 / 4 : ℝ) * (‖u ^ 2 - Q * v‖ₑ⁻¹ ^ (9 / 8 : ℝ) +
      ‖u ^ 2 - Q * v‖ₑ⁻¹ ^ (7 / 8 : ℝ) + ‖u ^ 2 - Q * v‖ₑ⁻¹ ^ (3 / 4 : ℝ))

/-- **The `u`-integral of `G`** (the note's `L_t` bounds inside its `J_{a,t}`), for `|v| < 1`. -/
theorem setLIntegral_G_le {K : ℝ} (hK : FullPlaneQuadratic (9 / 8) K) (hK0 : 0 ≤ K) (Q : ℂ)
    {v : ℂ} (hv : ‖v‖ < 1) :
    ∫⁻ u in ball (0 : ℂ) 1, G Q u v ≤
      ENNReal.ofReal (Lc K) * ‖v‖ₑ⁻¹ ^ (15 / 8 : ℝ) *
        (4 * ‖Q‖ₑ⁻¹ ^ (1 / 8 : ℝ) +
          ENNReal.ofReal ((1 + ‖Q‖) ^ (1 / 4 : ℝ)) * ‖Q‖ₑ⁻¹ ^ (1 / 2 : ℝ)) := by
  set r := ENNReal.ofReal ((1 + ‖Q‖) ^ (1 / 4 : ℝ))
  have hm : ∀ t : ℝ, Measurable fun u : ℂ => ‖u ^ 2 - Q * v‖ₑ⁻¹ ^ t := fun t => by fun_prop
  have eG : ∫⁻ u in ball (0 : ℂ) 1, G Q u v =
      ‖v‖ₑ⁻¹ ^ (4 / 3 : ℝ) * L 1 (Q * v) + r * (‖v‖ₑ⁻¹ ^ (5 / 4 : ℝ) * L (9 / 8) (Q * v)) +
        ‖v‖ₑ⁻¹ ^ (7 / 4 : ℝ) *
          (L (9 / 8) (Q * v) + L (7 / 8) (Q * v) + L (3 / 4) (Q * v)) := by
    unfold G L
    rw [lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop),
      lintegral_const_mul _ (hm _), lintegral_const_mul _ (by fun_prop),
      lintegral_const_mul _ (hm _), lintegral_const_mul _ (by fun_prop),
      lintegral_add_left (by fun_prop), lintegral_add_left (hm _)]
  set B := ENNReal.ofReal (Lc K) * ‖v‖ₑ⁻¹ ^ (15 / 8 : ℝ)
  have t8 : ∀ {t a : ℝ}, 1 / 8 ≤ t → t ≤ 9 / 8 → 0 ≤ a → a ≤ 7 / 4 →
      ‖v‖ₑ⁻¹ ^ a * L t (Q * v) ≤ B * ‖Q‖ₑ⁻¹ ^ (1 / 8 : ℝ) := by
    intro t a ht1 ht2 ha0 ha1
    refine (rpow_mul_L_le hK hK0 (by linarith) ht2 le_rfl ht1 ha0 (by linarith) Q hv).trans
      (le_of_eq ?_)
    simp only [B]; ring
  have h1 := t8 (t := 1) (a := 4 / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : ‖v‖ₑ⁻¹ ^ (5 / 4 : ℝ) * L (9 / 8) (Q * v) ≤ B * ‖Q‖ₑ⁻¹ ^ (1 / 2 : ℝ) := by
    refine (rpow_mul_L_le (t := 9 / 8) (s := 1 / 2) (a := 5 / 4) hK hK0 (by norm_num) le_rfl
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) Q hv).trans (le_of_eq ?_)
    simp only [B]; ring
  have h3 := t8 (t := 9 / 8) (a := 7 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h4 := t8 (t := 7 / 8) (a := 7 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 := t8 (t := 3 / 4) (a := 7 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [eG]
  calc ‖v‖ₑ⁻¹ ^ (4 / 3 : ℝ) * L 1 (Q * v) + r * (‖v‖ₑ⁻¹ ^ (5 / 4 : ℝ) * L (9 / 8) (Q * v)) +
        ‖v‖ₑ⁻¹ ^ (7 / 4 : ℝ) * (L (9 / 8) (Q * v) + L (7 / 8) (Q * v) + L (3 / 4) (Q * v))
      = ‖v‖ₑ⁻¹ ^ (4 / 3 : ℝ) * L 1 (Q * v) + r * (‖v‖ₑ⁻¹ ^ (5 / 4 : ℝ) * L (9 / 8) (Q * v)) +
        (‖v‖ₑ⁻¹ ^ (7 / 4 : ℝ) * L (9 / 8) (Q * v) + ‖v‖ₑ⁻¹ ^ (7 / 4 : ℝ) * L (7 / 8) (Q * v) +
          ‖v‖ₑ⁻¹ ^ (7 / 4 : ℝ) * L (3 / 4) (Q * v)) := by ring
    _ ≤ B * ‖Q‖ₑ⁻¹ ^ (1 / 8 : ℝ) + r * (B * ‖Q‖ₑ⁻¹ ^ (1 / 2 : ℝ)) +
        (B * ‖Q‖ₑ⁻¹ ^ (1 / 8 : ℝ) + B * ‖Q‖ₑ⁻¹ ^ (1 / 8 : ℝ) + B * ‖Q‖ₑ⁻¹ ^ (1 / 8 : ℝ)) := by
        gcongr
    _ = _ := by ring

/-- `(1 + |Q|)^{1/4} |Q|^{-1/2} ≤ |Q|^{-1/2} + |Q|^{-1/4}`. -/
theorem ofReal_one_add_rpow_mul_le (Q : ℂ) :
    ENNReal.ofReal ((1 + ‖Q‖) ^ (1 / 4 : ℝ)) * ‖Q‖ₑ⁻¹ ^ (1 / 2 : ℝ) ≤
      ‖Q‖ₑ⁻¹ ^ (1 / 2 : ℝ) + ‖Q‖ₑ⁻¹ ^ (1 / 4 : ℝ) := by
  rcases eq_or_ne Q 0 with rfl | hQ
  · rw [enorm_zero_inv_rpow (by norm_num), top_add]; exact le_top
  have hQ' : 0 < ‖Q‖ := norm_pos_iff.mpr hQ
  rw [enorm_inv_rpow_of_ne_zero hQ, enorm_inv_rpow_of_ne_zero hQ,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e1 : (1 + ‖Q‖) ^ (1 / 4 : ℝ) ≤ 1 + ‖Q‖ ^ (1 / 4 : ℝ) :=
    (Real.rpow_add_le_add_rpow (by norm_num) hQ'.le (by norm_num) (by norm_num)).trans_eq
      (by rw [Real.one_rpow])
  have e2 : ‖Q‖ ^ (1 / 4 : ℝ) * ‖Q‖ ^ (-(1 / 2 : ℝ)) = ‖Q‖ ^ (-(1 / 4 : ℝ)) :=
    rpow_mul_rpow_eq hQ' (by norm_num)
  calc (1 + ‖Q‖) ^ (1 / 4 : ℝ) * ‖Q‖ ^ (-(1 / 2 : ℝ))
      ≤ (1 + ‖Q‖ ^ (1 / 4 : ℝ)) * ‖Q‖ ^ (-(1 / 2 : ℝ)) := by gcongr
    _ = _ := by rw [add_mul, one_mul, e2]

/-- The bound on the suffix kernel `N₂`: `|Q|^{-1/8}` four times, `|Q|^{-1/2}` and `|Q|^{-1/4}`. -/
noncomputable def N2b (Q : ℂ) : ℝ≥0∞ :=
  4 * ‖Q‖ₑ⁻¹ ^ (1 / 8 : ℝ) + ‖Q‖ₑ⁻¹ ^ (1 / 2 : ℝ) + ‖Q‖ₑ⁻¹ ^ (1 / 4 : ℝ)

/-- **The note's `J` bounds, assembled** (Lemma "Weighted two-form suffix" after the `z`-step):
`∫∫_{|u|, |v| < 1} G(Q, u, v) ≤ 16π (2K + 4π) N2b(Q)`. -/
theorem lintegral_G_le {K : ℝ} (hK : FullPlaneQuadratic (9 / 8) K) (hK0 : 0 ≤ K) (Q : ℂ) :
    ∫⁻ v in ball (0 : ℂ) 1, ∫⁻ u in ball (0 : ℂ) 1, G Q u v ≤
      ENNReal.ofReal (16 * π * Lc K) * N2b Q := by
  set X := 4 * ‖Q‖ₑ⁻¹ ^ (1 / 8 : ℝ) +
    ENNReal.ofReal ((1 + ‖Q‖) ^ (1 / 4 : ℝ)) * ‖Q‖ₑ⁻¹ ^ (1 / 2 : ℝ)
  calc ∫⁻ v in ball (0 : ℂ) 1, ∫⁻ u in ball (0 : ℂ) 1, G Q u v
      ≤ ∫⁻ v in ball (0 : ℂ) 1, ENNReal.ofReal (Lc K) * X * ‖v‖ₑ⁻¹ ^ (15 / 8 : ℝ) :=
        setLIntegral_mono' measurableSet_ball fun v hv =>
          (setLIntegral_G_le hK hK0 Q (mem_ball_zero_iff.mp hv)).trans_eq (by ring)
    _ = ENNReal.ofReal (Lc K) * X * ENNReal.ofReal (16 * π) := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_ball_inv_rpow (by norm_num) one_pos,
          Real.one_rpow]
        congr 2
        norm_num
        ring
    _ ≤ ENNReal.ofReal (Lc K) * N2b Q * ENNReal.ofReal (16 * π) := by
        gcongr
        simp only [X, N2b, add_assoc]
        gcongr
        exact ofReal_one_add_rpow_mul_le Q
    _ = _ := by
        rw [show 16 * π * Lc K = Lc K * (16 * π) by ring, ENNReal.ofReal_mul (Lc_pos hK0).le]
        ring

/-- **`N2b` on a unit disc**, uniformly in the centre: `∫_{|Q - Q₀| < 1} N2b ≤ 18π`. -/
theorem setLIntegral_N2b_le (Q₀ : ℂ) : ∫⁻ Q in ball Q₀ 1, N2b Q ≤ ENNReal.ofReal (18 * π) := by
  unfold N2b
  rw [lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop),
    lintegral_const_mul _ (by fun_prop)]
  calc 4 * (∫⁻ Q in ball Q₀ 1, ‖Q‖ₑ⁻¹ ^ (1 / 8 : ℝ)) + (∫⁻ Q in ball Q₀ 1, ‖Q‖ₑ⁻¹ ^ (1 / 2 : ℝ)) +
        ∫⁻ Q in ball Q₀ 1, ‖Q‖ₑ⁻¹ ^ (1 / 4 : ℝ)
      ≤ 4 * ENNReal.ofReal (3 * π) + ENNReal.ofReal (3 * π) + ENNReal.ofReal (3 * π) := by
        gcongr <;> exact setLIntegral_ball_inv_rpow_le_three_pi Q₀ (by norm_num) (by norm_num)
    _ = _ := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end SLT.MiddlePositions.Two
