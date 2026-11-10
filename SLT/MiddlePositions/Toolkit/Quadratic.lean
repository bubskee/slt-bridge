/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Defs
public import SLT.PositionFour.Upstream.Cusp

/-!
# Planar powers and quadratics at a general exponent (note §2, Lemma "Planar powers and quadratics")

* `quadConstT_lt_top`: `K_t = ∫_ℂ |z² - 1|^{-t} dz < ∞` for `1 < t < 2`;
* `lintegral_quadratic_eq_rpow`: for `A ≠ 0`, `Δ = B² - 4AD ≠ 0` and any real `t`,
  `∫_ℂ |A z² + B z + D|^{-t} dz = 4^{t-1} |A|^{t-2} |Δ|^{1-t} K_t` (the argument of
  `SLT.PositionFour.lintegral_quadratic_eq`, which is the case `t = 4/3`);
* `fullPlaneQuadratic`: the interface statement `FullPlaneQuadratic t C` for every `1 < t < 2`,
  with the explicit constant `quadC t = 4^{t-1} (K_t + 1)`;
* `lintegral_closedBall_rpow_sub_le_rpow`: the shifted disc at exponent `0 < p < 2`,
  `∫_{|z| ≤ ρ} |z - w|^{-p} dz ≤ L_p ρ^{2-p}` uniformly in `w` (the note's item 1, used by the
  local finiteness of `F`).
-/

@[expose] public section

namespace SLT.MiddlePositions

open MeasureTheory Set Metric SLT.PositionFour
open scoped ENNReal

/-! ### The reference quadratic -/

/-- The constant `K_t = ∫_ℂ |z² - 1|^{-t} dz`. -/
noncomputable def quadConstT (t : ℝ) : ℝ≥0∞ := ∫⁻ z : ℂ, ‖z ^ 2 - 1‖ₑ ^ (-t)

/-- `K_t < ∞` for `1 < t < 2`: two singular points of order `t < 2`, decay `|z|^{-2t}` with
`2t > 2`. -/
theorem quadConstT_lt_top {t : ℝ} (ht1 : 1 < t) (ht2 : t < 2) : quadConstT t < ∞ := by
  have h := lintegral_twoPoint_lt_top (a := 1) (b := -1) (by norm_num) (p := t) (q := t)
    (c := 0) ht2 ht2 le_rfl (by linarith)
  refine lt_of_eq_of_lt (lintegral_congr fun z => ?_) h
  rw [show z ^ 2 - 1 = (z - 1) * (z - -1) by ring, enorm_mul,
    ENNReal.mul_rpow_of_ne_top enorm_ne_top enorm_ne_top]
  simp

/-! ### The full-plane quadratic integral -/

/-- **The full-plane quadratic integral at exponent `t`.** For `A ≠ 0` and `Δ = B² - 4AD ≠ 0`,
`∫ |A z² + B z + D|^{-t} dz = 4^{t-1} |A|^{t-2} |Δ|^{1-t} K_t`. -/
theorem lintegral_quadratic_eq_rpow {A B D : ℂ} (hA : A ≠ 0) (hΔ : B ^ 2 - 4 * A * D ≠ 0)
    (t : ℝ) :
    ∫⁻ v : ℂ, ‖A * v ^ 2 + B * v + D‖ₑ ^ (-t) =
      ENNReal.ofReal (4 ^ (t - 1) * ‖A‖ ^ (t - 2) * ‖B ^ 2 - 4 * A * D‖ ^ (1 - t)) *
        quadConstT t := by
  set Δ := B ^ 2 - 4 * A * D
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (Δ / (4 * A ^ 2)) two_pos
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hΔ
    have : Δ / (4 * A ^ 2) = 0 := by rw [← hd]; ring
    rwa [div_eq_zero_iff, or_iff_left (by simpa using hA)] at this
  set w₀ := B / (2 * A)
  set h : ℂ → ℝ≥0∞ := fun w => ‖A * d ^ 2 * ((w / d) ^ 2 - 1)‖ₑ ^ (-t)
  have hh : Measurable h := by fun_prop
  have hshift : ∀ v : ℂ, A * v ^ 2 + B * v + D = A * d ^ 2 * (((v + w₀) / d) ^ 2 - 1) := by
    intro v
    simp only [w₀]
    field_simp
    rw [hd]
    field_simp
    ring
  have hscale : ∀ z : ℂ, h (d * z) = ‖A * d ^ 2‖ₑ ^ (-t) * ‖z ^ 2 - 1‖ₑ ^ (-t) := by
    intro z
    simp only [h]
    rw [mul_div_cancel_left₀ z hd0, enorm_mul, ENNReal.mul_rpow_of_ne_top enorm_ne_top enorm_ne_top]
  have hnd : ENNReal.ofReal (Complex.normSq d) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Complex.normSq_pos.mpr hd0)
  have hint : ∫⁻ w, h w = ENNReal.ofReal (Complex.normSq d) * ∫⁻ z, h (d * z) := by
    rw [lintegral_comp_mul_left hd0 hh, ← mul_assoc,
      ENNReal.mul_inv_cancel hnd ENNReal.ofReal_ne_top, one_mul]
  have ha : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hδ : 0 < ‖Δ‖ := norm_pos_iff.mpr hΔ
  have hdn : ‖d‖ ^ 2 = ‖Δ‖ / (4 * ‖A‖ ^ 2) := by
    rw [← norm_pow, hd, norm_div, norm_mul, norm_pow]; norm_num
  have hreal : ‖d‖ ^ 2 * (‖A‖ * ‖d‖ ^ 2) ^ (-t) =
      4 ^ (t - 1) * ‖A‖ ^ (t - 2) * ‖Δ‖ ^ (1 - t) := by
    rw [hdn]
    set a := ‖A‖
    set δ := ‖Δ‖
    set s := δ / (4 * a ^ 2)
    have hs : 0 < s := by positivity
    have h4 : (0 : ℝ) < 4 * a ^ 2 := by positivity
    calc s * (a * s) ^ (-t)
        = a ^ (-t) * (s ^ (1 : ℝ) * s ^ (-t)) := by
          rw [Real.mul_rpow ha.le hs.le, Real.rpow_one]; ring
      _ = a ^ (-t) * s ^ (1 - t) := by rw [← Real.rpow_add hs]; ring_nf
      _ = a ^ (-t) * (δ ^ (1 - t) * (4 * a ^ 2) ^ (t - 1)) := by
          rw [Real.div_rpow hδ.le h4.le, show t - 1 = -(1 - t) by ring, Real.rpow_neg h4.le,
            div_eq_mul_inv]
      _ = a ^ (-t) * (δ ^ (1 - t) * (4 ^ (t - 1) * a ^ (2 * (t - 1)))) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast a 2,
            ← Real.rpow_mul ha.le]
          norm_num
      _ = 4 ^ (t - 1) * (a ^ (-t) * a ^ (2 * (t - 1))) * δ ^ (1 - t) := by ring
      _ = 4 ^ (t - 1) * a ^ (t - 2) * δ ^ (1 - t) := by
          rw [← Real.rpow_add ha]; ring_nf
  calc ∫⁻ v : ℂ, ‖A * v ^ 2 + B * v + D‖ₑ ^ (-t) = ∫⁻ v, h (v + w₀) := by
        simp_rw [hshift]; rfl
    _ = ∫⁻ w, h w := lintegral_add_right_eq_self h w₀
    _ = ENNReal.ofReal (Complex.normSq d) * (‖A * d ^ 2‖ₑ ^ (-t) * quadConstT t) := by
        rw [hint]; simp_rw [hscale]; rw [lintegral_const_mul _ (by fun_prop)]; rfl
    _ = _ := by
        rw [← mul_assoc]
        congr 1
        rw [← hreal, Complex.normSq_eq_norm_sq, ← ofReal_norm (A * d ^ 2),
          ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr (mul_ne_zero hA (pow_ne_zero 2 hd0))),
          ← ENNReal.ofReal_mul (by positivity),
          norm_mul, norm_pow]

/-- The constant of `fullPlaneQuadratic`: `4^{t-1} (K_t + 1)`. -/
noncomputable def quadC (t : ℝ) : ℝ := 4 ^ (t - 1) * ((quadConstT t).toReal + 1)

/-- `quadC t > 0`. -/
theorem quadC_pos (t : ℝ) : 0 < quadC t := by
  unfold quadC; positivity

/-- `‖z‖ₑ⁻¹ ^ a = ofReal (‖z‖ ^ (-a))` away from `0`. -/
theorem enorm_inv_rpow_eq_ofReal {z : ℂ} (hz : z ≠ 0) (a : ℝ) :
    ‖z‖ₑ⁻¹ ^ a = ENNReal.ofReal (‖z‖ ^ (-a)) := by
  rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg, enorm_rpow_eq_ofReal hz]

/-- **Interface 3, proved.** For `1 < t < 2` and `A ≠ 0`,
`∫_ℂ |A z² + B z + D|^{-t} ≤ C |A|^{t-2} |B² - 4AD|^{1-t}` with `C = quadC t`. -/
theorem fullPlaneQuadratic_quadC {t : ℝ} (ht1 : 1 < t) (ht2 : t < 2) :
    FullPlaneQuadratic t (quadC t) := by
  intro A B D hA
  have ha : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hCA : 0 < quadC t * ‖A‖ ^ (t - 2) := mul_pos (quadC_pos t) (by positivity)
  by_cases hΔ : B ^ 2 - 4 * A * D = 0
  · rw [hΔ, enorm_zero, ENNReal.inv_zero, ENNReal.top_rpow_of_pos (by linarith),
      ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hCA)]
    exact le_top
  have hK := quadConstT_lt_top ht1 ht2
  have hδ : 0 < ‖B ^ 2 - 4 * A * D‖ := norm_pos_iff.mpr hΔ
  have hlhs : ∫⁻ z : ℂ, ‖A * z ^ 2 + B * z + D‖ₑ⁻¹ ^ t =
      ∫⁻ z : ℂ, ‖A * z ^ 2 + B * z + D‖ₑ ^ (-t) :=
    lintegral_congr fun z => by rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]
  rw [hlhs, lintegral_quadratic_eq_rpow hA hΔ t, enorm_inv_rpow_eq_ofReal hΔ,
    ← ENNReal.ofReal_toReal hK.ne, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul hCA.le]
  refine ENNReal.ofReal_le_ofReal ?_
  have hK0 : 0 ≤ (quadConstT t).toReal := ENNReal.toReal_nonneg
  have e : -(t - 1) = 1 - t := by ring
  rw [e, quadC]
  have h1 : 0 ≤ 4 ^ (t - 1) * ‖A‖ ^ (t - 2) * ‖B ^ 2 - 4 * A * D‖ ^ (1 - t) := by positivity
  nlinarith

/-- **Interface 3, proved (existential form).** `∀ t ∈ (1, 2), ∃ C, FullPlaneQuadratic t C`. -/
theorem fullPlaneQuadratic : ∀ t : ℝ, 1 < t → t < 2 → ∃ C, FullPlaneQuadratic t C :=
  fun _ ht1 ht2 => ⟨_, fullPlaneQuadratic_quadC ht1 ht2⟩

/-! ### The shifted disc at exponent `p` -/

/-- The constant `L_p = ∫_{|z| < 1} |z|^{-p} + vol(closedBall 0 1)` of the shifted-disc bound. -/
noncomputable def discConstP (p : ℝ) : ℝ≥0∞ :=
  (∫⁻ z in ball (0 : ℂ) 1, ‖z‖ₑ ^ (-p)) + volume (closedBall (0 : ℂ) 1)

/-- `L_p < ∞` for `p < 2`. -/
theorem discConstP_lt_top {p : ℝ} (hp : p < 2) : discConstP p < ∞ :=
  ENNReal.add_lt_top.mpr ⟨lintegral_ball_rpow_neg_lt_top hp 1, measure_closedBall_lt_top⟩

/-- `∫_{|z| ≤ 1} |z - w|^{-p} dz ≤ L_p` for every `w`, for `p > 0`. -/
theorem lintegral_closedBall_one_rpow_sub_le_rpow {p : ℝ} (hp : 0 < p) (w : ℂ) :
    ∫⁻ z in closedBall (0 : ℂ) 1, ‖z - w‖ₑ ^ (-p) ≤ discConstP p := by
  have hpt : ∀ z : ℂ, (closedBall (0 : ℂ) 1).indicator (fun z => ‖z - w‖ₑ ^ (-p)) z ≤
      (ball w 1).indicator (fun z => ‖z - w‖ₑ ^ (-p)) z +
        (closedBall (0 : ℂ) 1).indicator 1 z := by
    intro z
    by_cases hz : z ∈ closedBall (0 : ℂ) 1
    · rw [indicator_of_mem hz, indicator_of_mem hz, Pi.one_apply]
      by_cases hzw : z ∈ ball w 1
      · rw [indicator_of_mem hzw]; exact le_self_add
      · rw [indicator_of_notMem hzw, zero_add]
        refine ENNReal.rpow_le_one_of_one_le_of_neg ?_ (by linarith)
        rw [mem_ball, dist_eq_norm, not_lt] at hzw
        rw [← ofReal_norm, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hzw
    · rw [indicator_of_notMem hz]; exact zero_le
  rw [← lintegral_indicator measurableSet_closedBall]
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_left ((by fun_prop : Measurable fun z : ℂ => ‖z - w‖ₑ ^ (-p)).indicator
    measurableSet_ball), lintegral_indicator_one measurableSet_closedBall, discConstP]
  refine add_le_add ?_ le_rfl
  rw [lintegral_indicator measurableSet_ball]
  have := lintegral_sub_right_eq_self (μ := (volume : Measure ℂ))
    ((ball (0 : ℂ) 1).indicator fun z : ℂ => ‖z‖ₑ ^ (-p)) w
  rw [lintegral_indicator measurableSet_ball] at this
  rw [← this, ← lintegral_indicator measurableSet_ball]
  refine le_of_eq (lintegral_congr fun z => ?_)
  simp only [indicator, mem_ball, dist_eq_norm, sub_zero]

/-- **The shifted disc at exponent `p`.** For `p > 0`, `ρ > 0` and every `w`,
`∫_{|z| ≤ ρ} |z - w|^{-p} dz ≤ L_p ρ^{2-p}`. -/
theorem lintegral_closedBall_rpow_sub_le_rpow {p : ℝ} (hp : 0 < p) (w : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∫⁻ z in closedBall (0 : ℂ) ρ, ‖z - w‖ₑ ^ (-p) ≤
      discConstP p * ENNReal.ofReal (ρ ^ (2 - p)) := by
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  set F : ℂ → ℝ≥0∞ := (closedBall (0 : ℂ) ρ).indicator fun z => ‖z - w‖ₑ ^ (-p)
  have hF : Measurable F := (by fun_prop : Measurable fun z : ℂ => ‖z - w‖ₑ ^ (-p)).indicator
    measurableSet_closedBall
  have hnρ : Complex.normSq (ρ : ℂ) = ρ ^ 2 := by rw [Complex.normSq_ofReal]; ring
  have hscale := lintegral_comp_mul_left hρc hF
  have hFρ : ∀ y : ℂ, F (ρ * y) = ENNReal.ofReal (ρ ^ (-p)) *
      (closedBall (0 : ℂ) 1).indicator (fun y => ‖y - w / ρ‖ₑ ^ (-p)) y := by
    intro y
    have hmem : ρ * y ∈ closedBall (0 : ℂ) ρ ↔ y ∈ closedBall (0 : ℂ) 1 := by
      simp only [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hρ.le]
      constructor
      · intro h; nlinarith [norm_nonneg y]
      · intro h; nlinarith [norm_nonneg y]
    simp only [F]
    by_cases hy : y ∈ closedBall (0 : ℂ) 1
    · rw [indicator_of_mem (hmem.mpr hy), indicator_of_mem hy]
      have : ρ * y - w = ρ * (y - w / ρ) := by field_simp
      rw [this, enorm_mul, ENNReal.mul_rpow_of_ne_top enorm_ne_top enorm_ne_top]
      congr 1
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hρ.le,
        ENNReal.ofReal_rpow_of_pos hρ]
    · rw [indicator_of_notMem (fun h => hy (hmem.mp h)), indicator_of_notMem hy, mul_zero]
  have hint : ∫⁻ z, F z = ENNReal.ofReal (ρ ^ 2) * ∫⁻ y, F (ρ * y) := by
    rw [hscale, hnρ, ← mul_assoc, ENNReal.mul_inv_cancel
      (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top, one_mul]
  rw [← lintegral_indicator measurableSet_closedBall]
  change ∫⁻ z, F z ≤ _
  rw [hint]
  simp_rw [hFρ]
  rw [lintegral_const_mul _ ((by fun_prop : Measurable fun y : ℂ =>
      ‖y - w / ρ‖ₑ ^ (-p)).indicator measurableSet_closedBall),
    lintegral_indicator measurableSet_closedBall]
  calc ENNReal.ofReal (ρ ^ 2) * (ENNReal.ofReal (ρ ^ (-p)) *
        ∫⁻ y in closedBall (0 : ℂ) 1, ‖y - w / ρ‖ₑ ^ (-p))
      ≤ ENNReal.ofReal (ρ ^ 2) * (ENNReal.ofReal (ρ ^ (-p)) * discConstP p) := by
        gcongr; exact lintegral_closedBall_one_rpow_sub_le_rpow hp _
    _ = discConstP p * ENNReal.ofReal (ρ ^ (2 - p)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_comm]
        congr 2
        rw [← Real.rpow_natCast, ← Real.rpow_add hρ]
        norm_num
        ring_nf

end SLT.MiddlePositions
