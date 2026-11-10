/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Defs
public import SLT.PositionFour.Downstream.Shell

/-!
# A shell corollary for any cubically homogeneous map (note §6)

`lintegral_homShell_lt_top_of_moment`: let `E` be a finite-dimensional real normed space of
dimension `n` with an additive Haar measure `μ`, and `R : E → V` continuous with
`‖R (c • w)‖ = c³ ‖R w‖` for `c > 0`. If `∫_{‖R w‖ < 1} ‖w‖^β dμ < ∞` for some `β ≥ 0`, then
`∫_{1/2 ≤ ‖w‖ < 1} ‖R w‖^{-2s} dμ < ∞` whenever `6s < n + β`.

This is `SLT.PositionFour.Downstream.shell_lintegral_lt_top_of_moment` (the position-four map on
`Row × Row`, `n = 24`) with the map, the space and the dimension made parameters; the dyadic
argument is the same (no polar coordinates). The boundedness of `R` on the unit ball, needed for
`s ≤ 0`, comes from continuity.

Applications (`shell_two`, `shell_three`): `R2` on `Row2 × Row2` and `R3` on `Row3 × Row3` are
continuous and cubic (`norm_R2_smul`, `norm_R3_smul`), both spaces have real dimension `24`, so
`SublevelTwo` (resp. `SublevelThree`), the moment at `β = 1/4`, gives the shell integral for every
`s < 97/24`, as in the note's §6.
-/

@[expose] public section

namespace SLT.MiddlePositions

open MeasureTheory Set Metric SLT.PositionFour
open scoped ENNReal NNReal Pointwise

section General

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup V]

/-- The sup-norm shell `{1/2 ≤ ‖w‖ < 1}` of a normed space. -/
def homShell (E : Type*) [Norm E] : Set E := {w | 1 / 2 ≤ ‖w‖ ∧ ‖w‖ < 1}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The shell is measurable. -/
theorem measurableSet_homShell : MeasurableSet (homShell E) :=
  (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

/-- The dyadic layer `{w ∈ shell : 8^k ‖R(w)‖ ≤ 1}`. -/
def homLayer (R : E → V) (k : ℕ) : Set E := {w | w ∈ homShell E ∧ 8 ^ k * ‖R w‖ ≤ 1}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The layers are measurable. -/
theorem measurableSet_homLayer {R : E → V} (hR : Continuous R) (k : ℕ) :
    MeasurableSet (homLayer R k) :=
  measurableSet_homShell.inter
    (measurableSet_le (hR.norm.measurable.const_mul _) measurable_const)

/-- **The layer volume bound**: `(2^k/4)^β (2^k/2)^n μ(A_k) ≤ ∫_{‖R‖ < 1} ‖w‖^β dμ`. -/
theorem homLayer_volume_le (μ : Measure E) [μ.IsAddHaarMeasure] {R : E → V}
    (hhom : ∀ c : ℝ, 0 < c → ∀ w, ‖R (c • w)‖ = c ^ 3 * ‖R w‖) {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) :
    ENNReal.ofReal ((2 ^ k / 4) ^ β * (2 ^ k / 2) ^ Module.finrank ℝ E) * μ (homLayer R k) ≤
      ∫⁻ w in {w : E | ‖R w‖ < 1}, ENNReal.ofReal (‖w‖ ^ β) ∂μ := by
  set c : ℝ := 2 ^ k / 2 with hc
  have hc0 : 0 < c := by positivity
  have hsub : c • homLayer R k ⊆ {w : E | ‖R w‖ < 1} := by
    rintro _ ⟨v, ⟨-, hv⟩, rfl⟩
    change ‖R (c • v)‖ < 1
    rw [hhom c hc0, hc, div_pow, ← pow_mul,
      show (2 : ℝ) ^ (k * 3) = 8 ^ k by rw [mul_comm, pow_mul]; norm_num]
    nlinarith [norm_nonneg (R v)]
  have hlow : ∀ w ∈ c • homLayer R k, ENNReal.ofReal ((2 ^ k / 4) ^ β) ≤
      ENNReal.ofReal (‖w‖ ^ β) := by
    rintro _ ⟨v, ⟨⟨hv1, -⟩, -⟩, rfl⟩
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) ?_ hβ)
    rw [norm_smul, Real.norm_of_nonneg hc0.le, hc]
    nlinarith [show (0 : ℝ) < 2 ^ k from by positivity]
  calc ENNReal.ofReal ((2 ^ k / 4) ^ β * c ^ Module.finrank ℝ E) * μ (homLayer R k)
      = ENNReal.ofReal ((2 ^ k / 4) ^ β) * μ (c • homLayer R k) := by
        rw [Measure.addHaar_smul_of_nonneg _ hc0.le, ENNReal.ofReal_mul (by positivity),
          mul_assoc]
    _ = ∫⁻ _ in c • homLayer R k, ENNReal.ofReal ((2 ^ k / 4) ^ β) ∂μ := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ w in c • homLayer R k, ENNReal.ofReal (‖w‖ ^ β) ∂μ :=
        setLIntegral_mono (by fun_prop) hlow
    _ ≤ _ := lintegral_mono_set hsub

/-- **The shell bound for a cubically homogeneous map.** If `R` is continuous with
`‖R (c • w)‖ = c³ ‖R w‖` for `c > 0`, `dim_ℝ E = n`, `β ≥ 0`, `6s < n + β` and
`∫_{‖R‖ < 1} ‖w‖^β dμ < ∞`, then `∫_{1/2 ≤ ‖w‖ < 1} ‖R w‖^{-2s} dμ < ∞`. -/
theorem lintegral_homShell_lt_top_of_moment (μ : Measure E) [μ.IsAddHaarMeasure] {R : E → V}
    (hRc : Continuous R) (hhom : ∀ c : ℝ, 0 < c → ∀ w, ‖R (c • w)‖ = c ^ 3 * ‖R w‖)
    {n : ℕ} (hn : Module.finrank ℝ E = n) {β s : ℝ} (hβ : 0 ≤ β) (hs : 6 * s < n + β)
    (hI : ∫⁻ w in {w : E | ‖R w‖ < 1}, ENNReal.ofReal (‖w‖ ^ β) ∂μ < ∞) :
    ∫⁻ w in homShell E, ‖R w‖ₑ⁻¹ ^ (2 * s) ∂μ < ∞ := by
  set I := ∫⁻ w in {w : E | ‖R w‖ < 1}, ENNReal.ofReal (‖w‖ ^ β) ∂μ
  have hvol_shell : μ (homShell E) < ∞ :=
    lt_of_le_of_lt (measure_mono fun _ hw => mem_ball_zero_iff.mpr hw.2) measure_ball_lt_top
  set a := 2 * s with ha
  rcases le_or_gt a 0 with ha0 | ha0
  · -- `s ≤ 0`: the integrand is bounded on the shell
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn
      hRc.continuousOn
    have hpt : ∀ w ∈ homShell E, ‖R w‖ₑ⁻¹ ^ a ≤ ENNReal.ofReal M ^ (-a) := by
      intro w hw
      rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]
      refine ENNReal.rpow_le_rpow ?_ (by linarith)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hM w (mem_closedBall_zero_iff.mpr hw.2.le))
    refine lt_of_le_of_lt (setLIntegral_mono measurable_const hpt) ?_
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)
      hvol_shell
  · set K : ℝ := (8 : ℝ) ^ a with hK
    have hK1 : 1 ≤ K := Real.one_le_rpow (by norm_num) ha0.le
    set f : ℕ → E → ℝ≥0∞ := fun k w =>
      ENNReal.ofReal (K ^ (k + 1)) * (homLayer R k).indicator 1 w with hf
    have hm : ∀ k : ℕ, Measurable (f k) := fun k =>
      (measurable_one.indicator (measurableSet_homLayer hRc k)).const_mul _
    -- the pointwise dyadic bound
    have hpt : ∀ w ∈ homShell E, ‖R w‖ₑ⁻¹ ^ a ≤ 1 + ∑' k : ℕ, f k w := by
      intro w hw
      have hx := norm_nonneg (R w)
      rcases le_or_gt 1 ‖R w‖ with hx1 | hx1
      · refine le_add_right (ENNReal.rpow_le_one ?_ ha0.le)
        rw [ENNReal.inv_le_one, ← ofReal_norm, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hx1
      rcases hx.eq_or_lt with hx0 | hx0
      · -- `R(w) = 0`: every layer contains `w`, and the series diverges
        have hall : ∀ k, w ∈ homLayer R k := fun k => ⟨hw, by rw [← hx0, mul_zero]; norm_num⟩
        have htop : ∑' k : ℕ, f k w = ⊤ := by
          refine top_le_iff.mp ?_
          calc (⊤ : ℝ≥0∞) = ∑' _ : ℕ, (1 : ℝ≥0∞) :=
                (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
            _ ≤ ∑' k : ℕ, f k w := ENNReal.tsum_le_tsum fun k => by
                simp only [hf, indicator_of_mem (hall k), Pi.one_apply, mul_one]
                exact ENNReal.one_le_ofReal.mpr (one_le_pow₀ hK1)
        rw [htop, add_top]; exact le_top
      · -- `0 < ‖R(w)‖ < 1`: `w` lies in the layer of its dyadic level
        obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near ((one_le_inv₀ hx0).mpr hx1.le)
          (by norm_num : (1 : ℝ) < 8)
        have hmem : w ∈ homLayer R m := ⟨hw, by
          have := mul_le_mul_of_nonneg_right hm1 hx0.le
          rwa [inv_mul_cancel₀ hx0.ne'] at this⟩
        refine le_trans ?_ (le_add_left (ENNReal.le_tsum m))
        simp only [hf, indicator_of_mem hmem, Pi.one_apply, mul_one]
        rw [← ofReal_norm, Downstream.ofReal_inv_rpow_of_pos hx0]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖R w‖ ^ (-a) = (‖R w‖⁻¹) ^ a := by
              rw [Real.inv_rpow hx, Real.rpow_neg hx]
          _ ≤ ((8 : ℝ) ^ (m + 1)) ^ a := Real.rpow_le_rpow (by positivity) hm2.le ha0.le
          _ = K ^ (m + 1) := by
              rw [hK, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
                ← Real.rpow_mul (by norm_num), mul_comm]
    -- the layer volumes
    set C : ℝ := 4 ^ β * 2 ^ n with hC
    set q : ℝ := (2 ^ β * 2 ^ n)⁻¹ with hq
    have hq0 : 0 < q := by positivity
    have hvol : ∀ k : ℕ, μ (homLayer R k) ≤ ENNReal.ofReal (C * q ^ k) * I := by
      intro k
      have h := homLayer_volume_le μ hhom hβ k
      rw [hn] at h
      have hM : (2 ^ k / 4 : ℝ) ^ β * (2 ^ k / 2) ^ n = (C * q ^ k)⁻¹ := by
        have h2k : ((2 : ℝ) ^ k) ^ β = (2 ^ β) ^ k := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
            Real.rpow_mul (by norm_num), Real.rpow_natCast]
        have e1 : ((2 : ℝ) ^ k / 4) ^ β = (2 ^ β) ^ k / 4 ^ β := by
          rw [Real.div_rpow (by positivity) (by norm_num), h2k]
        have e2 : ((2 : ℝ) ^ k / 2) ^ n = (2 ^ n) ^ k / 2 ^ n := by
          rw [div_pow, ← pow_mul, ← pow_mul, mul_comm k n]
        have e3 : C * q ^ k = 4 ^ β * 2 ^ n / ((2 ^ β) ^ k * (2 ^ n) ^ k) := by
          rw [hC, hq, inv_pow, mul_pow, div_eq_mul_inv]
        have hu : 0 < ((2 : ℝ) ^ β) ^ k := by positivity
        have hv : 0 < ((2 : ℝ) ^ n) ^ k := by positivity
        have hw : 0 < (4 : ℝ) ^ β := by positivity
        rw [e1, e2, e3]
        field_simp
      rw [hM] at h
      have hCq : 0 < C * q ^ k := by positivity
      calc μ (homLayer R k)
          = ENNReal.ofReal (C * q ^ k) *
              (ENNReal.ofReal (C * q ^ k)⁻¹ * μ (homLayer R k)) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hCq.le, mul_inv_cancel₀ hCq.ne',
              ENNReal.ofReal_one, one_mul]
        _ ≤ ENNReal.ofReal (C * q ^ k) * I := by gcongr
    -- the geometric ratio
    set ρ : ℝ := K * q with hρ
    have hρ0 : 0 ≤ ρ := by positivity
    have hρ1 : ρ < 1 := by
      have h8 : K = 2 ^ (3 * a) := by
        rw [hK, show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      have h2 : (2 : ℝ) ^ β * 2 ^ n = 2 ^ (β + n) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_natCast]
      rw [hρ, hq, h2, h8, ← div_eq_mul_inv, div_lt_one (by positivity)]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    calc ∫⁻ w in homShell E, ‖R w‖ₑ⁻¹ ^ a ∂μ
        ≤ ∫⁻ w in homShell E, (1 + ∑' k : ℕ, f k w) ∂μ :=
          setLIntegral_mono' measurableSet_homShell hpt
      _ = μ (homShell E) + ∑' k : ℕ, ENNReal.ofReal (K ^ (k + 1)) *
            μ (homLayer R k ∩ homShell E) := by
          rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul,
            lintegral_tsum fun k => (hm k).aemeasurable]
          congr 1
          refine tsum_congr fun k => ?_
          rw [lintegral_const_mul _ (measurable_one.indicator (measurableSet_homLayer hRc k)),
            lintegral_indicator_one (measurableSet_homLayer hRc k),
            Measure.restrict_apply (measurableSet_homLayer hRc k)]
      _ ≤ μ (homShell E) + ∑' k : ℕ, ENNReal.ofReal (K ^ (k + 1)) *
            (ENNReal.ofReal (C * q ^ k) * I) := by
          gcongr with k
          exact (measure_mono inter_subset_left).trans (hvol k)
      _ = μ (homShell E) + ENNReal.ofReal (K * C) * I * ∑' k : ℕ, ENNReal.ofReal ρ ^ k := by
          rw [← ENNReal.tsum_mul_left]
          congr 1
          refine tsum_congr fun k => ?_
          have key : K ^ (k + 1) * (C * q ^ k) = K * C * ρ ^ k := by
            rw [hρ, mul_pow, pow_succ]; ring
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), key,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hρ0, mul_right_comm]
      _ < ∞ := by
          rw [ENNReal.tsum_geometric]
          refine ENNReal.add_lt_top.mpr ⟨hvol_shell, ENNReal.mul_lt_top
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI) ?_⟩
          rw [ENNReal.inv_lt_top, tsub_pos_iff_lt, ← ENNReal.ofReal_one]
          exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr hρ1

/-- **The shell bound in dimension 24**: `2s < 8 + β/3` suffices. -/
theorem lintegral_homShell_lt_top_of_moment_24 (μ : Measure E) [μ.IsAddHaarMeasure] {R : E → V}
    (hRc : Continuous R) (hhom : ∀ c : ℝ, 0 < c → ∀ w, ‖R (c • w)‖ = c ^ 3 * ‖R w‖)
    (hn : Module.finrank ℝ E = 24) {β s : ℝ} (hβ : 0 ≤ β) (hs : 2 * s < 8 + β / 3)
    (hI : ∫⁻ w in {w : E | ‖R w‖ < 1}, ENNReal.ofReal (‖w‖ ^ β) ∂μ < ∞) :
    ∫⁻ w in homShell E, ‖R w‖ₑ⁻¹ ^ (2 * s) ∂μ < ∞ :=
  lintegral_homShell_lt_top_of_moment μ hRc hhom hn hβ (by push_cast; linarith) hI

end General

/-! ### The two middle positions -/

/-- `l ↦ l³` is cubic for real scalars. -/
theorem twoCube_smul (c : ℝ) (g : Form × Form) : twoCube (c • g) = (c ^ 3) • twoCube g := by
  simp only [twoCube, Prod.smul_fst, Prod.smul_snd, Downstream.cube_smul, smul_add]

/-- The generators are linear in the four cubics jointly. -/
theorem generators_smul (c : ℝ) (p₁ q₁ p₂ q₂ : Cubic) :
    generators (c • p₁) (c • q₁) (c • p₂) (c • q₂) = c • generators p₁ q₁ p₂ q₂ := by
  funext i
  fin_cases i <;> simp [generators, Complex.real_smul] <;> ring

/-- `R₂ (c w) = c³ R₂ w`. -/
theorem R2_smul (c : ℝ) (w : Row2 × Row2) : R2 (c • w) = (c ^ 3) • R2 w := by
  simp only [R2, Prod.smul_fst, Prod.smul_snd, Downstream.cube_smul, twoCube_smul,
    generators_smul]

/-- `R₃ (c w) = c³ R₃ w`. -/
theorem R3_smul (c : ℝ) (w : Row3 × Row3) : R3 (c • w) = (c ^ 3) • R3 w := by
  simp only [R3, Prod.smul_fst, Prod.smul_snd, Downstream.cube_smul, twoCube_smul,
    generators_smul]

/-- `‖R₂ (c w)‖ = c³ ‖R₂ w‖` for `c > 0`. -/
theorem norm_R2_smul {c : ℝ} (hc : 0 < c) (w : Row2 × Row2) : ‖R2 (c • w)‖ = c ^ 3 * ‖R2 w‖ := by
  rw [R2_smul, norm_smul, Real.norm_of_nonneg (by positivity)]

/-- `‖R₃ (c w)‖ = c³ ‖R₃ w‖` for `c > 0`. -/
theorem norm_R3_smul {c : ℝ} (hc : 0 < c) (w : Row3 × Row3) : ‖R3 (c • w)‖ = c ^ 3 * ‖R3 w‖ := by
  rw [R3_smul, norm_smul, Real.norm_of_nonneg (by positivity)]

/-- `generators` is continuous in the four cubics. -/
theorem continuous_generators :
    Continuous fun x : (Cubic × Cubic) × (Cubic × Cubic) =>
      generators x.1.1 x.1.2 x.2.1 x.2.2 := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp only [generators] <;> fun_prop

/-- `R₂` is continuous. -/
theorem continuous_R2 : Continuous R2 := by
  have hc : Continuous cube := by unfold cube; fun_prop
  have ht : Continuous twoCube := by unfold twoCube cube; fun_prop
  have : R2 = (fun x : (Cubic × Cubic) × (Cubic × Cubic) => generators x.1.1 x.1.2 x.2.1 x.2.2) ∘
      fun w : Row2 × Row2 => ((cube w.1.1, twoCube w.1.2), (cube w.2.1, twoCube w.2.2)) := rfl
  rw [this]
  exact continuous_generators.comp (by fun_prop)

/-- `R₃` is continuous. -/
theorem continuous_R3 : Continuous R3 := by
  have hc : Continuous cube := by unfold cube; fun_prop
  have ht : Continuous twoCube := by unfold twoCube cube; fun_prop
  have : R3 = (fun x : (Cubic × Cubic) × (Cubic × Cubic) => generators x.1.1 x.1.2 x.2.1 x.2.2) ∘
      fun w : Row3 × Row3 => ((twoCube w.1.1, cube w.1.2), (twoCube w.2.1, cube w.2.2)) := rfl
  rw [this]
  exact continuous_generators.comp (by fun_prop)

/-- `Row2 × Row2` has real dimension `24`. -/
theorem finrank_row2Pair : Module.finrank ℝ (Row2 × Row2) = 24 := by
  simp [Module.finrank_prod, Complex.finrank_real_complex]

/-- `Row3 × Row3` has real dimension `24`. -/
theorem finrank_row3Pair : Module.finrank ℝ (Row3 × Row3) = 24 := by
  simp [Module.finrank_prod, Complex.finrank_real_complex]

/-- The Borel structure on `Form`. -/
instance borelSpace_form : BorelSpace Form := Prod.borelSpace

/-- The Borel structure on `Form × Form`. -/
instance borelSpace_formPair : BorelSpace (Form × Form) := Prod.borelSpace

/-- The Borel structure on `Row2`. -/
instance borelSpace_row2 : BorelSpace Row2 := Prod.borelSpace

/-- The Borel structure on `Row3`. -/
instance borelSpace_row3 : BorelSpace Row3 := Prod.borelSpace

/-- The Borel structure on `Row2 × Row2`. -/
instance borelSpace_row2Pair : BorelSpace (Row2 × Row2) := Prod.borelSpace

/-- The Borel structure on `Row3 × Row3`. -/
instance borelSpace_row3Pair : BorelSpace (Row3 × Row3) := Prod.borelSpace

/-- Lebesgue measure on `Form` is an additive Haar measure. -/
instance isAddHaarMeasure_volume_form : (volume : Measure Form).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Lebesgue measure on `Row2 × Row2` is an additive Haar measure. -/
instance isAddHaarMeasure_volume_row2Pair : (volume : Measure (Row2 × Row2)).IsAddHaarMeasure := by
  have : (volume : Measure (Form × Form)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have : (volume : Measure Row2).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  exact Measure.prod.instIsAddHaarMeasure _ _

/-- Lebesgue measure on `Row3 × Row3` is an additive Haar measure. -/
instance isAddHaarMeasure_volume_row3Pair : (volume : Measure (Row3 × Row3)).IsAddHaarMeasure := by
  have : (volume : Measure (Form × Form)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have : (volume : Measure Row3).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  exact Measure.prod.instIsAddHaarMeasure _ _

/-- **The shell corollary at position two** (note §6): `SublevelTwo` gives
`∫_{1/2 ≤ ‖w‖ < 1} ‖R₂ w‖^{-2s} dw < ∞` for every `s < 97/24`. -/
theorem shell_two (h : SublevelTwo) {s : ℝ} (hs : s < 97 / 24) :
    ∫⁻ w in homShell (Row2 × Row2), ‖R2 w‖ₑ⁻¹ ^ (2 * s) < ∞ :=
  lintegral_homShell_lt_top_of_moment_24 volume continuous_R2 (fun _ hc w => norm_R2_smul hc w)
    finrank_row2Pair (β := 1 / 4) (by norm_num) (by linarith) h

/-- **The shell corollary at position three** (note §6): `SublevelThree` gives
`∫_{1/2 ≤ ‖w‖ < 1} ‖R₃ w‖^{-2s} dw < ∞` for every `s < 97/24`. -/
theorem shell_three (h : SublevelThree) {s : ℝ} (hs : s < 97 / 24) :
    ∫⁻ w in homShell (Row3 × Row3), ‖R3 w‖ₑ⁻¹ ^ (2 * s) < ∞ :=
  lintegral_homShell_lt_top_of_moment_24 volume continuous_R3 (fun _ hc w => norm_R3_smul hc w)
    finrank_row3Pair (β := 1 / 4) (by norm_num) (by linarith) h

end SLT.MiddlePositions
