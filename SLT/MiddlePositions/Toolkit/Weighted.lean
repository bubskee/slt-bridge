/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Defs
public import SLT.PositionFour.Upstream.TwoCube
public import SLT.PositionFour.Upstream.Sylvester
public import SLT.PositionFour.Upstream.Coords

/-!
# The weighted two-cube measure bound (note §2, Lemma "Weighted two-cube measure bound", first half)

`weightedTwoCubeBound`: the pushforward of `W₂ · Lebesgue` under `Ψ(l, m) = l³ + m³` is at most
`(16/9) F · Lebesgue`.

Route, as in the note:
1. a pointwise weight bound off `det g = 0` (`W2_le_of_det2_ne_zero`):
   `W₂(g) ≤ 1 + 8 ‖P‖^{1/4} |𝔇(P)|^{-1/24}` at `P = Ψ(g)`, from `norm_twoCube_cases`,
   `‖H(P)‖ ≤ 2 ‖P‖²` (`norm_hess_le`) and `𝔇(Ψ(g)) = det(g)⁶` (`disc_twoCube`);
2. this multiplier `twoCubeWeight` times `|𝔇|^{-4/3}` is at most `8 F` (`twoCubeWeight_mul_le`);
3. multiply into `lintegral_twoCube_le` (the integral form of `twoCubeBound`).

One simplification over the note: both cases of `norm_twoCube_cases` give the single bound
`‖g‖ |det g| ≤ 4 ‖Ψ(g)‖` (`norm_mul_norm_det2_le`), so the `‖P‖^{β/3}` term and the bound
`|𝔇(P)| ≤ 18 ‖P‖⁴` are not needed.
-/

@[expose] public section

namespace SLT.MiddlePositions

open MeasureTheory Set SLT.PositionFour
open scoped ENNReal

/-! ### Pointwise bounds -/

/-- `‖H(P)‖ ≤ 2 ‖P‖²`. -/
theorem norm_hess_le (P : Cubic) : ‖hess P‖ ≤ 2 * ‖P‖ ^ 2 := by
  have h : ∀ i j k l : Fin 4, ‖P i * P j - P k * P l‖ ≤ 2 * ‖P‖ ^ 2 := by
    intro i j k l
    have hi := norm_le_pi_norm P i
    have hj := norm_le_pi_norm P j
    have hk := norm_le_pi_norm P k
    have hl := norm_le_pi_norm P l
    calc ‖P i * P j - P k * P l‖ ≤ ‖P i‖ * ‖P j‖ + ‖P k‖ * ‖P l‖ := by
          rw [← norm_mul, ← norm_mul]; exact norm_sub_le _ _
      _ ≤ ‖P‖ * ‖P‖ + ‖P‖ * ‖P‖ := by gcongr
      _ = 2 * ‖P‖ ^ 2 := by ring
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  fin_cases i
  · simpa [hess, sq] using h 0 2 1 1
  · simpa [hess] using h 0 3 1 2
  · simpa [hess, sq] using h 1 3 2 2

/-- `|det g| ≤ 2 ‖g‖²` for the sup norm. -/
theorem norm_det2_le (g : Form × Form) : ‖det2 g‖ ≤ 2 * ‖g‖ ^ 2 := by
  have ha : ‖g.1.1‖ ≤ ‖g‖ := (norm_fst_le g.1).trans (norm_fst_le g)
  have hb : ‖g.1.2‖ ≤ ‖g‖ := (norm_snd_le g.1).trans (norm_fst_le g)
  have hc : ‖g.2.1‖ ≤ ‖g‖ := (norm_fst_le g.2).trans (norm_snd_le g)
  have hd : ‖g.2.2‖ ≤ ‖g‖ := (norm_snd_le g.2).trans (norm_snd_le g)
  calc ‖det2 g‖ ≤ ‖g.1.1‖ * ‖g.2.2‖ + ‖g.1.2‖ * ‖g.2.1‖ := by
        rw [det2, ← norm_mul, ← norm_mul]; exact norm_sub_le _ _
    _ ≤ ‖g‖ * ‖g‖ + ‖g‖ * ‖g‖ := by gcongr
    _ = 2 * ‖g‖ ^ 2 := by ring

/-- **The norm bound in one line.** `‖g‖ |det g| ≤ 4 ‖l³ + m³‖`, from either case of
`norm_twoCube_cases`. -/
theorem norm_mul_norm_det2_le (g : Form × Form) : ‖g‖ * ‖det2 g‖ ≤ 4 * ‖twoCube g‖ := by
  have hg := norm_nonneg g
  have hD := norm_nonneg (det2 g)
  have hP := norm_nonneg (twoCube g)
  rcases norm_twoCube_cases g with h | h
  · have := norm_det2_le g
    nlinarith [mul_le_mul_of_nonneg_left this hg]
  · have hH := norm_hess_le (twoCube g)
    have hsq : (‖g‖ * ‖det2 g‖) ^ 2 ≤ (4 * ‖twoCube g‖) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq

/-- `W₂(g) ≤ 1 + 4 ‖g‖^{1/4}`. -/
theorem W2_le (g : Form × Form) : W2 g ≤ 1 + 4 * ‖g‖ ^ (1 / 4 : ℝ) := by
  have ha : ‖g.1.1‖ ≤ ‖g‖ := (norm_fst_le g.1).trans (norm_fst_le g)
  have hb : ‖g.1.2‖ ≤ ‖g‖ := (norm_snd_le g.1).trans (norm_fst_le g)
  have hc : ‖g.2.1‖ ≤ ‖g‖ := (norm_fst_le g.2).trans (norm_snd_le g)
  have hd : ‖g.2.2‖ ≤ ‖g‖ := (norm_snd_le g.2).trans (norm_snd_le g)
  have e : ∀ x : ℝ, 0 ≤ x → x ≤ ‖g‖ → x ^ (1 / 4 : ℝ) ≤ ‖g‖ ^ (1 / 4 : ℝ) := fun x hx h =>
    Real.rpow_le_rpow hx h (by norm_num)
  have := e _ (norm_nonneg _) ha
  have := e _ (norm_nonneg _) hb
  have := e _ (norm_nonneg _) hc
  have := e _ (norm_nonneg _) hd
  unfold W2
  linarith

/-- `4^{1/4} ≤ 2`. -/
theorem four_rpow_quarter_le : (4 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
  calc (4 : ℝ) ^ (1 / 4 : ℝ) ≤ 16 ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num)
        (by norm_num)
    _ = 2 := by
        rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num

/-- **The pointwise weight bound.** Off `det g = 0`,
`W₂(g) ≤ 1 + 8 ‖P‖^{1/4} |𝔇(P)|^{-1/24}` at `P = l³ + m³`. -/
theorem W2_le_of_det2_ne_zero {g : Form × Form} (hg : det2 g ≠ 0) :
    W2 g ≤ 1 + 8 * ‖twoCube g‖ ^ (1 / 4 : ℝ) * ‖disc (twoCube g)‖ ^ (-(1 / 24 : ℝ)) := by
  have hD : 0 < ‖det2 g‖ := norm_pos_iff.mpr hg
  have hP := norm_nonneg (twoCube g)
  have hgle : ‖g‖ ≤ 4 * ‖twoCube g‖ * ‖det2 g‖⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hD]; exact norm_mul_norm_det2_le g
  have hdisc : ‖disc (twoCube g)‖ ^ (-(1 / 24 : ℝ)) = ‖det2 g‖⁻¹ ^ (1 / 4 : ℝ) := by
    rw [disc_twoCube, norm_pow, ← Real.rpow_natCast, ← Real.rpow_mul hD.le, Real.inv_rpow hD.le,
      ← Real.rpow_neg hD.le]
    norm_num
  have hq : ‖g‖ ^ (1 / 4 : ℝ) ≤
      2 * (‖twoCube g‖ ^ (1 / 4 : ℝ) * ‖det2 g‖⁻¹ ^ (1 / 4 : ℝ)) := by
    calc ‖g‖ ^ (1 / 4 : ℝ) ≤ (4 * ‖twoCube g‖ * ‖det2 g‖⁻¹) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (norm_nonneg _) hgle (by norm_num)
      _ = 4 ^ (1 / 4 : ℝ) * (‖twoCube g‖ ^ (1 / 4 : ℝ) * ‖det2 g‖⁻¹ ^ (1 / 4 : ℝ)) := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) hP,
            mul_assoc]
      _ ≤ 2 * (‖twoCube g‖ ^ (1 / 4 : ℝ) * ‖det2 g‖⁻¹ ^ (1 / 4 : ℝ)) := by
          gcongr; exact four_rpow_quarter_le
  rw [hdisc]
  have := W2_le g
  nlinarith

/-! ### The multiplier -/

/-- The multiplier `1 + 8 ‖P‖^{1/4} |𝔇(P)|^{-1/24}` (`∞` where `𝔇(P) = 0` and `P ≠ 0`). -/
noncomputable def twoCubeWeight (P : Cubic) : ℝ≥0∞ :=
  1 + ENNReal.ofReal (8 * ‖P‖ ^ (1 / 4 : ℝ)) * ((‖disc P‖₊ : ℝ≥0∞)⁻¹) ^ (1 / 24 : ℝ)

/-- The multiplier is measurable. -/
@[fun_prop] theorem measurable_twoCubeWeight : Measurable twoCubeWeight := by
  unfold twoCubeWeight disc; fun_prop

/-- Off `det g = 0`, `W₂(g) ≤ twoCubeWeight (Ψ g)`. -/
theorem ofReal_W2_le {g : Form × Form} (hg : det2 g ≠ 0) :
    ENNReal.ofReal (W2 g) ≤ twoCubeWeight (twoCube g) := by
  have hd : disc (twoCube g) ≠ 0 := by rw [disc_twoCube]; exact pow_ne_zero 6 hg
  rw [twoCubeWeight, inv_nnnorm_rpow, enorm_rpow_eq_ofReal hd, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
  exact ENNReal.ofReal_le_ofReal (W2_le_of_det2_ne_zero hg)

/-- `twoCubeWeight · |𝔇|^{-4/3} ≤ 8 F`, using `4/3 + 1/24 = 11/8`. -/
theorem twoCubeWeight_mul_le (P : Cubic) : twoCubeWeight P * twoCubeDensity P ≤ 8 * F P := by
  set x : ℝ≥0∞ := (‖disc P‖₊ : ℝ≥0∞)⁻¹
  set a : ℝ≥0∞ := ENNReal.ofReal (‖P‖ ^ (1 / 4 : ℝ))
  have h8 : ENNReal.ofReal (8 * ‖P‖ ^ (1 / 4 : ℝ)) = 8 * a := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hexp : x ^ (1 / 24 : ℝ) * x ^ (4 / 3 : ℝ) = x ^ (11 / 8 : ℝ) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num
  have hF : F P = x ^ (4 / 3 : ℝ) + a * x ^ (11 / 8 : ℝ) := rfl
  have hD : twoCubeDensity P = x ^ (4 / 3 : ℝ) := rfl
  rw [twoCubeWeight, h8, hF, hD]
  calc (1 + 8 * a * x ^ (1 / 24 : ℝ)) * x ^ (4 / 3 : ℝ)
      = x ^ (4 / 3 : ℝ) + 8 * (a * (x ^ (1 / 24 : ℝ) * x ^ (4 / 3 : ℝ))) := by ring
    _ = x ^ (4 / 3 : ℝ) + 8 * (a * x ^ (11 / 8 : ℝ)) := by rw [hexp]
    _ ≤ 8 * x ^ (4 / 3 : ℝ) + 8 * (a * x ^ (11 / 8 : ℝ)) := by
        gcongr; exact le_mul_of_one_le_left zero_le (by norm_num)
    _ = 8 * (x ^ (4 / 3 : ℝ) + a * x ^ (11 / 8 : ℝ)) := by ring

/-! ### The measure bound -/

/-- **The weighted two-cube bound, integral form.** For measurable `φ ≥ 0`,
`∫ W₂(g) φ(Ψ g) dg ≤ (16/9) ∫ φ(P) F(P) dP`. -/
theorem lintegral_W2_twoCube_le {φ : Cubic → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ g : Form × Form, ENNReal.ofReal (W2 g) * φ (twoCube g) ≤
      ENNReal.ofReal (16 / 9) * ∫⁻ P, φ P * F P := by
  have hae : ∀ᵐ g : Form × Form, det2 g ≠ 0 := by
    refine ae_iff.mpr ?_
    simpa using volume_det2_eq_zero
  calc ∫⁻ g : Form × Form, ENNReal.ofReal (W2 g) * φ (twoCube g)
      ≤ ∫⁻ g : Form × Form, (fun P => φ P * twoCubeWeight P) (twoCube g) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with g hg
        rw [mul_comm]
        gcongr
        exact ofReal_W2_le hg
    _ ≤ ENNReal.ofReal (2 / 9) * ∫⁻ P, φ P * twoCubeWeight P * twoCubeDensity P :=
        lintegral_twoCube_le (hφ.mul measurable_twoCubeWeight)
    _ ≤ ENNReal.ofReal (2 / 9) * ∫⁻ P, 8 * (φ P * F P) := by
        gcongr 1
        refine lintegral_mono fun P => ?_
        calc φ P * twoCubeWeight P * twoCubeDensity P
            = φ P * (twoCubeWeight P * twoCubeDensity P) := mul_assoc _ _ _
          _ ≤ φ P * (8 * F P) := mul_le_mul_right (twoCubeWeight_mul_le P) _
          _ = 8 * (φ P * F P) := by ring
    _ = ENNReal.ofReal (16 / 9) * ∫⁻ P, φ P * F P := by
        rw [lintegral_const_mul' _ _ (by norm_num), ← mul_assoc]
        congr 1
        rw [show (16 / 9 : ℝ) = 2 / 9 * 8 by norm_num, ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_ofNat]

/-- **Interface 1, proved, with the constant `16/9`.** -/
theorem weightedTwoCubeBound_sixteen_ninths : WeightedTwoCubeBound (16 / 9) := by
  refine Measure.le_iff.mpr fun A hA => ?_
  have hm : Measurable twoCube := by unfold twoCube cube; fun_prop
  rw [Measure.map_apply hm hA, withDensity_apply _ (hm hA), Measure.smul_apply,
    withDensity_apply _ hA, smul_eq_mul]
  have h := lintegral_W2_twoCube_le (φ := A.indicator 1) (measurable_one.indicator hA)
  have e1 : ∫⁻ g in twoCube ⁻¹' A, ENNReal.ofReal (W2 g) =
      ∫⁻ g : Form × Form, ENNReal.ofReal (W2 g) * A.indicator 1 (twoCube g) := by
    rw [← lintegral_indicator (hm hA)]
    refine lintegral_congr fun g => ?_
    by_cases hg : twoCube g ∈ A
    · rw [indicator_of_mem (show g ∈ twoCube ⁻¹' A from hg), indicator_of_mem hg, Pi.one_apply,
        mul_one]
    · rw [indicator_of_notMem (show g ∉ twoCube ⁻¹' A from hg), indicator_of_notMem hg,
        mul_zero]
  have e2 : ∫⁻ P, A.indicator 1 P * F P = ∫⁻ P in A, F P := by
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun P => ?_
    by_cases hP : P ∈ A <;> simp [hP]
  rw [e1]
  rw [e2] at h
  exact h

/-- **Interface 1, proved (existential form).** -/
theorem weightedTwoCubeBound : ∃ C, WeightedTwoCubeBound C :=
  ⟨_, weightedTwoCubeBound_sixteen_ninths⟩

end SLT.MiddlePositions
