/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Downstream.Finiteness
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The angular margin on the shell

The form of the threshold that paper 2 consumes: for every `s < 13/3`,
`‖R(w)‖^{-2s}` is integrable on the shell `{1/2 ≤ ‖w‖ < 1}` of `Row × Row` (sup norm, the library's
shell convention of `SLT/Template/Margin.lean`). This is `shell_lintegral_lt_top` (`ℝ≥0∞` form) and
`integrableOn_shell` (Bochner form), from the weighted sublevel finiteness of Section 3 and cubic
homogeneity `R(c w) = c³ R(w)`.

The note derives it from the exact polar identity
`I_β = (24 + β)⁻¹ ∫_{S²³} ‖R(ω)‖^{-8-β/3} dσ(ω)`. Here only the needed inequality is proved, by
a dyadic argument that avoids spherical coordinates:

* scaling by `c = 2^k/2` maps `A_k = {w ∈ shell : 8^k ‖R(w)‖ ≤ 1}` into the unit sublevel set,
  where `‖w‖ ≥ 2^k/4`; so `vol(A_k) ≲ I_β 2^{-k(24+β)}` with
  `I_β = ∫_{‖R‖ < 1} ‖w‖^β < ∞`;
* `‖R‖^{-2s} ≤ 1 + ∑_k 8^{2s(k+1)} 𝟙_{A_k}` on the shell, and the series of volumes converges
  when `6s < 24 + β`.

Taking `β ∈ (6s - 24, 2)` gives every `s < 13/3`.
-/

@[expose] public section

namespace SLT.PositionFour.Downstream

open MeasureTheory Set Real Metric
open scoped ENNReal NNReal Pointwise

/-! ### Homogeneity and size of the leading map -/

/-- Cubes are cubic: `cube (c l) = c³ cube l`. -/
theorem cube_smul (c : ℝ) (l : Form) : cube (c • l) = (c ^ 3) • cube l := by
  funext i
  fin_cases i <;> simp [cube, Complex.real_smul] <;> ring

/-- The row cubic is cubic: `T (c r) = c³ T r`. -/
theorem rowCubic_smul (c : ℝ) (r : Row) : rowCubic (c • r) = (c ^ 3) • rowCubic r := by
  simp only [rowCubic, Pi.smul_apply, cube_smul, Finset.smul_sum]

/-- **Cubic homogeneity of the leading map**: `R (c w) = c³ R w`. -/
theorem leadingMap_smul (c : ℝ) (w : Row × Row) :
    leadingMap (c • w) = (c ^ 3) • leadingMap w := by
  funext i
  fin_cases i <;>
    simp [leadingMap, Prod.smul_fst, Prod.smul_snd, rowCubic_smul, smul_sub]

/-- `‖R (c w)‖ = |c|³ ‖R w‖`. -/
theorem norm_leadingMap_smul (c : ℝ) (w : Row × Row) :
    ‖leadingMap (c • w)‖ = |c| ^ 3 * ‖leadingMap w‖ := by
  rw [leadingMap_smul, norm_smul, Real.norm_eq_abs, abs_pow]

/-- On the closed unit ball, each cube has components of norm at most one. -/
theorem norm_cube_le_one {l : Form} (hl : ‖l‖ ≤ 1) (j : Fin 4) : ‖cube l j‖ ≤ 1 := by
  have h1 : ‖l.1‖ ≤ 1 := (norm_fst_le l).trans hl
  have h2 : ‖l.2‖ ≤ 1 := (norm_snd_le l).trans hl
  have p1 : ‖l.1‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) h1
  have p2 : ‖l.2‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) h2
  have n1 := norm_nonneg l.1
  have n2 := norm_nonneg l.2
  fin_cases j
  · change ‖l.1 ^ 3‖ ≤ 1
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) h1
  · change ‖l.1 ^ 2 * l.2‖ ≤ 1
    rw [norm_mul, norm_pow]; nlinarith
  · change ‖l.1 * l.2 ^ 2‖ ≤ 1
    rw [norm_mul, norm_pow]; nlinarith
  · change ‖l.2 ^ 3‖ ≤ 1
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) h2

/-- On the closed unit ball, each row-cubic component has norm at most three. -/
theorem norm_rowCubic_le {r : Row} (hr : ‖r‖ ≤ 1) (j : Fin 4) : ‖rowCubic r j‖ ≤ 3 := by
  simp only [rowCubic, Finset.sum_apply]
  calc ‖∑ i, cube (r i) j‖ ≤ ∑ i : Fin 3, ‖cube (r i) j‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => norm_cube_le_one ((norm_le_pi_norm r i).trans hr) j
    _ = 3 := by simp

/-- `‖R(w)‖ ≤ 6` on the closed unit ball. -/
theorem norm_leadingMap_le {w : Row × Row} (hw : ‖w‖ ≤ 1) : ‖leadingMap w‖ ≤ 6 := by
  have h1 : ‖w.1‖ ≤ 1 := (norm_fst_le w).trans hw
  have h2 : ‖w.2‖ ≤ 1 := (norm_snd_le w).trans hw
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_
  have hsub : ∀ j, ‖rowCubic w.1 j - rowCubic w.2 j‖ ≤ 6 := fun j =>
    (norm_sub_le _ _).trans (by linarith [norm_rowCubic_le h1 j, norm_rowCubic_le h2 j])
  fin_cases i
  · exact hsub 0
  · exact hsub 1
  · change ‖rowCubic w.1 2‖ ≤ 6
    linarith [norm_rowCubic_le h1 2]
  · change ‖rowCubic w.1 3‖ ≤ 6
    linarith [norm_rowCubic_le h1 3]
  · change ‖rowCubic w.2 2‖ ≤ 6
    linarith [norm_rowCubic_le h2 2]
  · change ‖rowCubic w.2 3‖ ≤ 6
    linarith [norm_rowCubic_le h2 3]

/-- The leading map is continuous. -/
theorem continuous_leadingMap : Continuous leadingMap := by
  have : Continuous rowCubic := by unfold rowCubic cube; fun_prop
  exact continuous_cubicMap.comp (this.prodMap this)

/-- The raw norm is dominated by the row weights: `‖w‖^β ≤ W_β(w₁) + W_β(w₂)` for `β ≥ 0`. -/
theorem norm_rpow_le_rowWeight {β : ℝ} (hβ : 0 ≤ β) (w : Row × Row) :
    ‖w‖ ^ β ≤ rowWeight β w.1 + rowWeight β w.2 := by
  have hrow : ∀ r : Row, ‖r‖ ^ β ≤ rowWeight β r := by
    intro r
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => ‖r i‖)
      Finset.univ_nonempty
    have hle : ‖r‖ ≤ ‖r j‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => hj i (Finset.mem_univ _)
    calc ‖r‖ ^ β ≤ ‖r j‖ ^ β := Real.rpow_le_rpow (norm_nonneg _) hle hβ
      _ ≤ rowWeight β r := Finset.single_le_sum (f := fun i => ‖r i‖ ^ β)
          (fun i _ => Real.rpow_nonneg (norm_nonneg _) _) (Finset.mem_univ j)
  have h1 := hrow w.1
  have h2 := hrow w.2
  have n1 := rowWeight_nonneg β w.1
  have n2 := rowWeight_nonneg β w.2
  rw [Prod.norm_def]
  rcases le_total ‖w.1‖ ‖w.2‖ with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-! ### Volume on `Row × Row` -/

/-- Lebesgue measure on `Row × Row` is an additive Haar measure. -/
instance isAddHaarMeasure_volume_rowPair :
    (volume : Measure (Row × Row)).IsAddHaarMeasure := by
  have : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have : (volume : Measure Row).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.prod.instIsAddHaarMeasure _ _

/-- `Row × Row` has real dimension `24`. -/
theorem finrank_rowPair : Module.finrank ℝ (Row × Row) = 24 := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype]
  simp [Module.finrank_prod, Complex.finrank_real_complex]

/-- Real scaling multiplies volume on `Row × Row` by `c²⁴`. -/
theorem volume_smul_rowPair {c : ℝ} (hc : 0 ≤ c) (A : Set (Row × Row)) :
    volume (c • A) = ENNReal.ofReal (c ^ 24) * volume A := by
  rw [Measure.addHaar_smul_of_nonneg _ hc, finrank_rowPair]

/-! ### The shell -/

/-- The shell `{1/2 ≤ ‖w‖ < 1}` of `Row × Row` (sup norm), as in `SLT.Template.shell`. -/
def rowShell : Set (Row × Row) := {w | 1 / 2 ≤ ‖w‖ ∧ ‖w‖ < 1}

/-- The shell is measurable. -/
theorem measurableSet_rowShell : MeasurableSet rowShell :=
  (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

/-- The shell has finite volume. -/
theorem volume_rowShell_lt_top : volume rowShell < ∞ :=
  lt_of_le_of_lt (measure_mono fun _ hw => mem_ball_zero_iff.mpr hw.2) measure_ball_lt_top

/-- The dyadic layer `A_k = {w ∈ shell : 8^k ‖R(w)‖ ≤ 1}`. -/
def shellLayer (k : ℕ) : Set (Row × Row) := {w | w ∈ rowShell ∧ 8 ^ k * ‖leadingMap w‖ ≤ 1}

/-- The layers are measurable. -/
theorem measurableSet_shellLayer (k : ℕ) : MeasurableSet (shellLayer k) :=
  measurableSet_rowShell.inter
    (measurableSet_le (continuous_leadingMap.norm.measurable.const_mul _) measurable_const)

/-- **The layer volume bound**: `(2^k/4)^β (2^k/2)^24 vol(A_k) ≤ ∫_{‖R‖ < 1} ‖w‖^β`. Scaling by
`c = 2^k/2` maps `A_k` into the unit sublevel set, onto points with `‖w‖ ≥ 2^k/4`. -/
theorem shellLayer_volume_le {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) :
    ENNReal.ofReal ((2 ^ k / 4) ^ β * (2 ^ k / 2) ^ 24) * volume (shellLayer k) ≤
      ∫⁻ w in {w : Row × Row | ‖leadingMap w‖ < 1}, ENNReal.ofReal (‖w‖ ^ β) := by
  set c : ℝ := 2 ^ k / 2 with hc
  have hc0 : 0 < c := by positivity
  have hsub : c • shellLayer k ⊆ {w : Row × Row | ‖leadingMap w‖ < 1} := by
    rintro _ ⟨v, ⟨-, hv⟩, rfl⟩
    rw [mem_ofPred_eq, norm_leadingMap_smul, abs_of_pos hc0, hc, div_pow, ← pow_mul,
      show (2 : ℝ) ^ (k * 3) = 8 ^ k by rw [mul_comm, pow_mul]; norm_num]
    nlinarith [norm_nonneg (leadingMap v)]
  have hlow : ∀ w ∈ c • shellLayer k, ENNReal.ofReal ((2 ^ k / 4) ^ β) ≤
      ENNReal.ofReal (‖w‖ ^ β) := by
    rintro _ ⟨v, ⟨⟨hv1, -⟩, -⟩, rfl⟩
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) ?_ hβ)
    rw [norm_smul, Real.norm_of_nonneg hc0.le, hc]
    nlinarith [show (0 : ℝ) < 2 ^ k from by positivity]
  calc ENNReal.ofReal ((2 ^ k / 4) ^ β * c ^ 24) * volume (shellLayer k)
      = ENNReal.ofReal ((2 ^ k / 4) ^ β) * volume (c • shellLayer k) := by
        rw [volume_smul_rowPair hc0.le, ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ = ∫⁻ _ in c • shellLayer k, ENNReal.ofReal ((2 ^ k / 4) ^ β) := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ w in c • shellLayer k, ENNReal.ofReal (‖w‖ ^ β) :=
        setLIntegral_mono (by fun_prop) hlow
    _ ≤ _ := lintegral_mono_set hsub

/-- **The shell bound, given the weighted sublevel integral**: if `I_β = ∫_{‖R‖<1} ‖w‖^β` is finite
for some `β ≥ 0` with `2s < 8 + β/3`, then `∫_{shell} ‖R‖^{-2s} < ∞`. -/
theorem shell_lintegral_lt_top_of_moment {β s : ℝ} (hβ : 0 ≤ β) (hs : 2 * s < 8 + β / 3)
    (hI : ∫⁻ w in {w : Row × Row | ‖leadingMap w‖ < 1}, ENNReal.ofReal (‖w‖ ^ β) < ∞) :
    ∫⁻ w in rowShell, ‖leadingMap w‖ₑ⁻¹ ^ (2 * s) < ∞ := by
  set I := ∫⁻ w in {w : Row × Row | ‖leadingMap w‖ < 1}, ENNReal.ofReal (‖w‖ ^ β)
  set a := 2 * s with ha
  rcases le_or_gt a 0 with ha0 | ha0
  · -- `s ≤ 0`: the integrand is bounded by `6^{-a}` on the shell
    have hpt : ∀ w ∈ rowShell, ‖leadingMap w‖ₑ⁻¹ ^ a ≤ ENNReal.ofReal 6 ^ (-a) := by
      intro w hw
      rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]
      refine ENNReal.rpow_le_rpow ?_ (by linarith)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_leadingMap_le hw.2.le)
    refine lt_of_le_of_lt (setLIntegral_mono measurable_const hpt) ?_
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)
      volume_rowShell_lt_top
  · set E : ℝ := (8 : ℝ) ^ a with hE
    have hE1 : 1 ≤ E := Real.one_le_rpow (by norm_num) ha0.le
    set f : ℕ → Row × Row → ℝ≥0∞ := fun k w =>
      ENNReal.ofReal (E ^ (k + 1)) * (shellLayer k).indicator 1 w with hf
    have hm : ∀ k : ℕ, Measurable (f k) := fun k =>
      (measurable_one.indicator (measurableSet_shellLayer k)).const_mul _
    -- the pointwise dyadic bound
    have hpt : ∀ w ∈ rowShell, ‖leadingMap w‖ₑ⁻¹ ^ a ≤ 1 + ∑' k : ℕ, f k w := by
      intro w hw
      have hx := norm_nonneg (leadingMap w)
      rcases le_or_gt 1 ‖leadingMap w‖ with hx1 | hx1
      · refine le_add_right (ENNReal.rpow_le_one ?_ ha0.le)
        rw [ENNReal.inv_le_one, ← ofReal_norm, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hx1
      rcases hx.eq_or_lt with hx0 | hx0
      · -- `R(w) = 0`: every layer contains `w`, and the series diverges
        have hall : ∀ k, w ∈ shellLayer k := fun k => ⟨hw, by rw [← hx0, mul_zero]; norm_num⟩
        have htop : ∑' k : ℕ, f k w = ⊤ := by
          refine top_le_iff.mp ?_
          calc (⊤ : ℝ≥0∞) = ∑' _ : ℕ, (1 : ℝ≥0∞) :=
                (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
            _ ≤ ∑' k : ℕ, f k w := ENNReal.tsum_le_tsum fun k => by
                simp only [hf, indicator_of_mem (hall k), Pi.one_apply, mul_one]
                exact ENNReal.one_le_ofReal.mpr (one_le_pow₀ hE1)
        rw [htop, add_top]; exact le_top
      · -- `0 < ‖R(w)‖ < 1`: `w` lies in the layer of its dyadic level
        obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near ((one_le_inv₀ hx0).mpr hx1.le)
          (by norm_num : (1 : ℝ) < 8)
        have hmem : w ∈ shellLayer n := ⟨hw, by
          have := mul_le_mul_of_nonneg_right hn1 hx0.le
          rwa [inv_mul_cancel₀ hx0.ne'] at this⟩
        refine le_trans ?_ (le_add_left (ENNReal.le_tsum n))
        simp only [hf, indicator_of_mem hmem, Pi.one_apply, mul_one]
        rw [← ofReal_norm, ofReal_inv_rpow_of_pos hx0]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖leadingMap w‖ ^ (-a) = (‖leadingMap w‖⁻¹) ^ a := by
              rw [Real.inv_rpow hx, Real.rpow_neg hx]
          _ ≤ ((8 : ℝ) ^ (n + 1)) ^ a := Real.rpow_le_rpow (by positivity) hn2.le ha0.le
          _ = E ^ (n + 1) := by
              rw [hE, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
                ← Real.rpow_mul (by norm_num), mul_comm]
    -- the layer volumes
    set C : ℝ := 4 ^ β * 2 ^ 24 with hC
    set q : ℝ := (2 ^ β * 2 ^ 24)⁻¹ with hq
    have hq0 : 0 < q := by positivity
    have hvol : ∀ k : ℕ, volume (shellLayer k) ≤ ENNReal.ofReal (C * q ^ k) * I := by
      intro k
      have h := shellLayer_volume_le hβ k
      have hM : (2 ^ k / 4 : ℝ) ^ β * (2 ^ k / 2) ^ 24 = (C * q ^ k)⁻¹ := by
        have h2k : ((2 : ℝ) ^ k) ^ β = (2 ^ β) ^ k := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
            Real.rpow_mul (by norm_num), Real.rpow_natCast]
        have e1 : ((2 : ℝ) ^ k / 4) ^ β = (2 ^ β) ^ k / 4 ^ β := by
          rw [Real.div_rpow (by positivity) (by norm_num), h2k]
        have e2 : ((2 : ℝ) ^ k / 2) ^ 24 = (2 ^ 24) ^ k / 2 ^ 24 := by
          rw [div_pow, ← pow_mul, ← pow_mul, mul_comm]
        have e3 : C * q ^ k = 4 ^ β * 2 ^ 24 / ((2 ^ β) ^ k * (2 ^ 24) ^ k) := by
          rw [hC, hq, inv_pow, mul_pow, div_eq_mul_inv]
        have hu : 0 < ((2 : ℝ) ^ β) ^ k := by positivity
        have hv : 0 < ((2 : ℝ) ^ 24) ^ k := by positivity
        have hw : 0 < (4 : ℝ) ^ β := by positivity
        rw [e1, e2, e3]
        field_simp
      rw [hM] at h
      have hCq : 0 < C * q ^ k := by positivity
      calc volume (shellLayer k)
          = ENNReal.ofReal (C * q ^ k) *
              (ENNReal.ofReal (C * q ^ k)⁻¹ * volume (shellLayer k)) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hCq.le, mul_inv_cancel₀ hCq.ne',
              ENNReal.ofReal_one, one_mul]
        _ ≤ ENNReal.ofReal (C * q ^ k) * I := by gcongr
    -- the geometric ratio
    set ρ : ℝ := E * q with hρ
    have hρ0 : 0 ≤ ρ := by positivity
    have hρ1 : ρ < 1 := by
      have h8 : E = 2 ^ (3 * a) := by
        rw [hE, show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      have h2 : (2 : ℝ) ^ β * 2 ^ 24 = 2 ^ (β + 24) := by
        rw [Real.rpow_add (by norm_num), show (2 : ℝ) ^ (24 : ℝ) = 2 ^ 24 by norm_cast]
      rw [hρ, hq, h2, h8, ← div_eq_mul_inv, div_lt_one (by positivity)]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    have hI' : I ≠ ⊤ := hI.ne
    calc ∫⁻ w in rowShell, ‖leadingMap w‖ₑ⁻¹ ^ a
        ≤ ∫⁻ w in rowShell, (1 + ∑' k : ℕ, f k w) :=
          setLIntegral_mono' measurableSet_rowShell hpt
      _ = volume rowShell + ∑' k : ℕ, ENNReal.ofReal (E ^ (k + 1)) *
            volume (shellLayer k ∩ rowShell) := by
          rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul,
            lintegral_tsum fun k => (hm k).aemeasurable]
          congr 1
          refine tsum_congr fun k => ?_
          rw [lintegral_const_mul _ (measurable_one.indicator (measurableSet_shellLayer k)),
            lintegral_indicator_one (measurableSet_shellLayer k),
            Measure.restrict_apply (measurableSet_shellLayer k)]
      _ ≤ volume rowShell + ∑' k : ℕ, ENNReal.ofReal (E ^ (k + 1)) *
            (ENNReal.ofReal (C * q ^ k) * I) := by
          gcongr with k
          exact (measure_mono inter_subset_left).trans (hvol k)
      _ = volume rowShell + ENNReal.ofReal (E * C) * I * ∑' k : ℕ, ENNReal.ofReal ρ ^ k := by
          rw [← ENNReal.tsum_mul_left]
          congr 1
          refine tsum_congr fun k => ?_
          have key : E ^ (k + 1) * (C * q ^ k) = E * C * ρ ^ k := by
            rw [hρ, mul_pow, pow_succ]; ring
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), key,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hρ0, mul_right_comm]
      _ < ∞ := by
          rw [ENNReal.tsum_geometric]
          refine ENNReal.add_lt_top.mpr ⟨volume_rowShell_lt_top, ENNReal.mul_lt_top
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI) ?_⟩
          rw [ENNReal.inv_lt_top, tsub_pos_iff_lt, ← ENNReal.ofReal_one]
          exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr hρ1

/-- **The angular margin on the shell** (`ℝ≥0∞` form). Given the density interface at the
weights `0` and `β`, with `0 ≤ β < 2` and `2s < 8 + β/3`:
`∫_{1/2 ≤ ‖w‖ < 1} ‖R(w)‖^{-2s} dw < ∞`. -/
theorem shell_lintegral_lt_top {s β C₀ C : ℝ} (hβ0 : 0 ≤ β) (hβ2 : β < 2)
    (hs : 2 * s < 8 + β / 3) (hD₀ : DensityBound 0 C₀) (hDβ : DensityBound β C)
    (hL₀ : LocallyFiniteRow 0) (hLβ : LocallyFiniteRow β) :
    ∫⁻ w in rowShell, ‖leadingMap w‖ₑ⁻¹ ^ (2 * s) < ∞ := by
  refine shell_lintegral_lt_top_of_moment hβ0 hs (lt_of_le_of_lt ?_
    (sublevel_weighted_lt_top hβ0 hβ2 hD₀ hDβ hL₀ hLβ))
  refine setLIntegral_mono (by
    have h := measurable_rowWeight β
    fun_prop) fun w _ => ENNReal.ofReal_le_ofReal (norm_rpow_le_rowWeight hβ0 w)

/-- **The angular margin for every `s < 13/3`**, given the density interface at every weight
`β ∈ [0, 2)`. The weight used is `β = max 0 ((6s - 22)/2)`. -/
theorem shell_lintegral_lt_top_of_interface {s : ℝ} (hs : s < 13 / 3)
    (h : ∀ β : ℝ, 0 ≤ β → β < 2 → ∃ C, DensityBound β C ∧ LocallyFiniteRow β) :
    ∫⁻ w in rowShell, ‖leadingMap w‖ₑ⁻¹ ^ (2 * s) < ∞ := by
  set β := max 0 ((6 * s - 22) / 2) with hβ
  have hβ0 : 0 ≤ β := le_max_left _ _
  have hβ2 : β < 2 := max_lt (by norm_num) (by linarith)
  have hsβ : 2 * s < 8 + β / 3 := by
    rcases le_total 0 ((6 * s - 22) / 2) with h' | h'
    · rw [hβ, max_eq_right h']; linarith
    · rw [hβ, max_eq_left h']; linarith
  obtain ⟨C₀, hD₀, hL₀⟩ := h 0 le_rfl (by norm_num)
  obtain ⟨C, hD, hL⟩ := h β hβ0 hβ2
  exact shell_lintegral_lt_top hβ0 hβ2 hsβ hD₀ hD hL₀ hL

/-- `ofReal (x^{-a}) ≤ x^{-a}` in `ℝ≥0∞` (the real power is `0` at `x = 0`). -/
theorem ofReal_rpow_neg_le {x : ℝ} (hx : 0 ≤ x) (a : ℝ) :
    ENNReal.ofReal (x ^ (-a)) ≤ (ENNReal.ofReal x)⁻¹ ^ a := by
  rcases hx.eq_or_lt with rfl | hx
  · rcases lt_trichotomy a 0 with ha | rfl | ha
    · rw [Real.zero_rpow (by linarith), ENNReal.ofReal_zero]; exact bot_le
    · simp
    · rw [Real.zero_rpow (by linarith), ENNReal.ofReal_zero]; exact bot_le
  · rw [ofReal_inv_rpow_of_pos hx]

/-- **The angular margin on the shell** (Bochner form): `‖R‖^{-2s}` is integrable on the shell. -/
theorem integrableOn_shell {s β C₀ C : ℝ} (hβ0 : 0 ≤ β) (hβ2 : β < 2)
    (hs : 2 * s < 8 + β / 3) (hD₀ : DensityBound 0 C₀) (hDβ : DensityBound β C)
    (hL₀ : LocallyFiniteRow 0) (hLβ : LocallyFiniteRow β) :
    IntegrableOn (fun w => ‖leadingMap w‖ ^ (-(2 * s))) rowShell := by
  refine ⟨(continuous_leadingMap.norm.measurable.pow_const _).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun w => ?_)
    (shell_lintegral_lt_top hβ0 hβ2 hs hD₀ hDβ hL₀ hLβ)
  rw [Real.enorm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), ← ofReal_norm]
  exact ofReal_rpow_neg_le (norm_nonneg _) _

end SLT.PositionFour.Downstream
