/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Laplace.Integral

/-!
# The LLC identity, log-averaged form (brief 01, stage L)

For a finite measure `ν` (prior times cutoff) and a measurable loss `K ≥ 0` (a.e.), put

* `Zr ν K t = ∫ e^{-t K} dν` (real-valued partition function; `Z ν K t = ofReal (Zr ν K t)`),
* `gibbsMean ν K t = E_t[K] = ∫ K e^{-t K} dν / Zr ν K t` (the tempered-posterior mean loss).

**L1** (`hasDerivAt_log_Zr`): for `t > 0` and `ν ≠ 0`, `(log Z)'(t) = -E_t[K]`.
No boundedness of `K` is needed: `u e^{-s u} ≤ 1/s` for `u ≥ 0`, `s > 0` gives the domination.

**L2** (`llc_log_average`, `tendsto_llc_log_average`): if `Z` has learning pair `(λ, m)` then,
for any fixed `t₀ > 0`,
`∫_{t₀}^{T} E_t[K] dt = λ log T - (m-1) log log T + O(1)`, hence
`(1/log T) ∫_{t₀}^{T} E_t[K] dt → λ`.
Since `E_t[K] dt = (t E_t[K]) dt/t`, this says the log-average of `t · E_t[K]` is `λ`; the
multiplicity `m` appears in the `log log T` term.

**Scope.** This is the *population, deterministic* statement about the exact loss `K` and the exact
tempered posterior `e^{-tK} dν / Z(t)`. It is not a statement about the SGLD estimator of the LLC,
which uses the empirical loss at inverse temperature `β = 1/log n`.
-/

@[expose] public section

namespace SLT

open MeasureTheory Filter Topology Real Set

variable {α : Type*} [MeasurableSpace α] {ν : Measure α} {K : α → ℝ}

/-- The real partition function `Z(t) = ∫ e^{-t K} dν` (Bochner). -/
noncomputable def Zr (ν : Measure α) (K : α → ℝ) (t : ℝ) : ℝ := ∫ x, Real.exp (-(t * K x)) ∂ν

/-- The unnormalised mean loss `∫ K e^{-t K} dν`. -/
noncomputable def gibbsNum (ν : Measure α) (K : α → ℝ) (t : ℝ) : ℝ :=
  ∫ x, K x * Real.exp (-(t * K x)) ∂ν

/-- The tempered-posterior mean loss `E_t[K] = ∫ K e^{-t K} dν / Z(t)`. -/
noncomputable def gibbsMean (ν : Measure α) (K : α → ℝ) (t : ℝ) : ℝ :=
  gibbsNum ν K t / Zr ν K t

/-- `u e^{-s u} ≤ 1/s` for `u ≥ 0`, `s > 0`. -/
theorem mul_exp_neg_mul_le {s u : ℝ} (hs : 0 < s) (_hu : 0 ≤ u) :
    u * Real.exp (-(s * u)) ≤ 1 / s := by
  have h1 : s * u ≤ Real.exp (s * u) := by linarith [Real.add_one_le_exp (s * u)]
  have hp := Real.exp_pos (s * u)
  rw [le_div_iff₀ hs, Real.exp_neg]
  have : u * (Real.exp (s * u))⁻¹ * s = (s * u) / Real.exp (s * u) := by ring
  rw [this, div_le_one hp]
  exact h1

section Finite

variable [IsFiniteMeasure ν]

/-- For finite `ν`, nonnegative `K` and `t ≥ 0`, `Z = ofReal (Zr)`. -/
theorem Z_eq_ofReal_Zr (hK : Measurable K) (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) {t : ℝ} (ht : 0 ≤ t) :
    Z ν K t = ENNReal.ofReal (Zr ν K t) :=
  Z_eq_ofReal_integral (integrable_exp_neg_mul hK hK0 ht)

/-- `Zr > 0` for finite nonzero `ν`, nonnegative `K` and `t ≥ 0`. -/
theorem Zr_pos (hK : Measurable K) (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) (hν : ν ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    0 < Zr ν K t := by
  unfold Zr
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le)
    (integrable_exp_neg_mul hK hK0 ht)]
  have : Function.support (fun x => Real.exp (-(t * K x))) = univ := by
    ext x; simp [Real.exp_ne_zero]
  rw [this]
  exact Measure.measure_univ_pos.mpr hν

private theorem integrable_mul_exp_neg_mul (hK : Measurable K) (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) {t : ℝ}
    (ht : 0 < t) : Integrable (fun x => K x * Real.exp (-(t * K x))) ν := by
  refine Integrable.of_bound (by fun_prop : Measurable _).aestronglyMeasurable (1 / t) ?_
  filter_upwards [hK0] with x hx
  rw [Real.norm_of_nonneg (mul_nonneg hx (Real.exp_pos _).le)]
  exact mul_exp_neg_mul_le ht hx

omit [IsFiniteMeasure ν] in
/-- The Gibbs numerator of a nonnegative loss is nonnegative. -/
theorem gibbsNum_nonneg (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) (t : ℝ) : 0 ≤ gibbsNum ν K t :=
  integral_nonneg_of_ae (by filter_upwards [hK0] with x hx using mul_nonneg hx (Real.exp_pos _).le)

omit [IsFiniteMeasure ν] in
/-- The Gibbs mean of a nonnegative loss is nonnegative. -/
theorem gibbsMean_nonneg (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) (t : ℝ) : 0 ≤ gibbsMean ν K t :=
  div_nonneg (gibbsNum_nonneg hK0 t) (integral_nonneg fun _ => (Real.exp_pos _).le)

omit [IsFiniteMeasure ν] in
/-- Domination on `s > t/2`: `|K e^{-s K}| ≤ 2/t`. -/
private theorem norm_mul_exp_neg_le (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂ν, ∀ s, t / 2 < s → ‖K x * Real.exp (-(s * K x))‖ ≤ 2 / t := by
  filter_upwards [hK0] with x hx s hs
  rw [Real.norm_of_nonneg (mul_nonneg hx (Real.exp_pos _).le)]
  have hs0 : 0 < s := by linarith
  calc _ ≤ 1 / s := mul_exp_neg_mul_le hs0 hx
    _ ≤ 2 / t := by rw [div_le_div_iff₀ hs0 ht]; linarith

/-- `Z'(t) = -∫ K e^{-t K} dν` for `t > 0`. -/
theorem hasDerivAt_Zr (hK : Measurable K) (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (Zr ν K) (-gibbsNum ν K t) t := by
  have hb : ∀ᵐ x ∂ν, ∀ s ∈ Metric.ball t (t / 2),
      ‖-(K x * Real.exp (-(s * K x)))‖ ≤ 2 / t := by
    filter_upwards [norm_mul_exp_neg_le hK0 ht] with x hx s hs
    rw [norm_neg]
    refine hx s ?_
    rw [Metric.mem_ball, Real.dist_eq] at hs
    linarith [(abs_lt.mp hs).1]
  have hd : ∀ᵐ x ∂ν, ∀ s ∈ Metric.ball t (t / 2),
      HasDerivAt (fun s => Real.exp (-(s * K x))) (-(K x * Real.exp (-(s * K x)))) s := by
    refine Eventually.of_forall fun x s _ => ?_
    have h1 := ((hasDerivAt_id' s).const_mul (-K x)).exp
    have e : (fun y => Real.exp (-K x * y)) = (fun s => Real.exp (-(s * K x))) := by
      funext y; ring_nf
    rw [e] at h1
    convert h1 using 1
    ring_nf
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := t)
    (F := fun s x => Real.exp (-(s * K x))) (F' := fun s x => -(K x * Real.exp (-(s * K x))))
    (bound := fun _ => 2 / t) (Metric.ball_mem_nhds t (half_pos ht))
    (Eventually.of_forall fun s =>
      (by fun_prop : Measurable fun x => Real.exp (-(s * K x))).aestronglyMeasurable)
    (integrable_exp_neg_mul hK hK0 ht.le)
    (by fun_prop : Measurable fun x => -(K x * Real.exp (-(t * K x)))).aestronglyMeasurable
    hb (integrable_const _) hd
  have e : gibbsNum ν K t = -∫ x, -(K x * Real.exp (-(t * K x))) ∂ν := by
    rw [integral_neg, neg_neg]; rfl
  rw [e, neg_neg]
  exact key.2

/-- **L1. The LLC identity**: `(log Z)'(t) = -E_t[K]` for `t > 0`. -/
theorem hasDerivAt_log_Zr (hK : Measurable K) (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) (hν : ν ≠ 0) {t : ℝ}
    (ht : 0 < t) : HasDerivAt (fun s => Real.log (Zr ν K s)) (-gibbsMean ν K t) t := by
  have := (hasDerivAt_Zr hK hK0 ht).log (Zr_pos hK hK0 hν ht.le).ne'
  rwa [neg_div] at this

private theorem continuousAt_gibbsNum (hK : Measurable K) (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) {t : ℝ}
    (ht : 0 < t) : ContinuousAt (gibbsNum ν K) t := by
  refine continuousAt_of_dominated (bound := fun _ => 2 / t)
    (Eventually.of_forall fun s =>
      (by fun_prop : Measurable fun x => K x * Real.exp (-(s * K x))).aestronglyMeasurable)
    ?_ (integrable_const _) (Eventually.of_forall fun x => by fun_prop)
  filter_upwards [Ioi_mem_nhds (half_lt_self ht)] with s hs
  filter_upwards [norm_mul_exp_neg_le hK0 ht] with x hx using hx s hs

/-- The Gibbs mean `E_t[K]` is continuous on `t > 0`. -/
theorem continuousOn_gibbsMean (hK : Measurable K) (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) (hν : ν ≠ 0) :
    ContinuousOn (gibbsMean ν K) (Ioi 0) := fun _ ht =>
  ((continuousAt_gibbsNum hK hK0 ht).div (hasDerivAt_Zr hK hK0 ht).continuousAt
    (Zr_pos hK hK0 hν (le_of_lt ht)).ne').continuousWithinAt

/-- (L1) **Integrated identity**: `∫_{t₀}^{T} E_t[K] dt = log Z(t₀) - log Z(T)` for `t₀, T > 0`. -/
theorem integral_gibbsMean (hK : Measurable K) (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) (hν : ν ≠ 0)
    {t₀ T : ℝ} (ht₀ : 0 < t₀) (hT : 0 < T) :
    ∫ t in t₀..T, gibbsMean ν K t = Real.log (Zr ν K t₀) - Real.log (Zr ν K T) := by
  have hsub : uIcc t₀ T ⊆ Ioi 0 := fun s hs => by
    rcases le_total t₀ T with h | h
    · rw [uIcc_of_le h] at hs; exact lt_of_lt_of_le ht₀ hs.1
    · rw [uIcc_of_ge h] at hs; exact lt_of_lt_of_le hT hs.1
  have hint : IntervalIntegrable (fun t => -gibbsMean ν K t) volume t₀ T :=
    ((continuousOn_gibbsMean hK hK0 hν).mono hsub).neg.intervalIntegrable
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hasDerivAt_log_Zr hK hK0 hν (hsub hs)) hint
  rw [intervalIntegral.integral_neg] at this
  linarith

end Finite

/-! ### L2. The log-averaged identity -/

/-- `log rate λ m T = -λ log T + (m - 1) log log T` for `T > 1`. -/
theorem log_rate {lam : ℝ} {m : ℕ} (hm : 1 ≤ m) {T : ℝ} (hT : 1 < T) :
    Real.log (rate lam m T) = -lam * Real.log T + ((m : ℝ) - 1) * Real.log (Real.log T) := by
  have hl : 0 < Real.log T := Real.log_pos hT
  rw [rate, Real.log_mul (Real.rpow_pos_of_pos (by linarith) _).ne' (pow_pos hl _).ne',
    Real.log_rpow (by linarith), Real.log_pow, Nat.cast_sub hm, Nat.cast_one]

/-- `Zr` is the Bochner partition function used by `HasLaplaceOrder`. -/
theorem Zr_eq_integral : (fun N => ∫ x, Real.exp (-N * K x) ∂ν) = Zr ν K := by
  funext N; simp only [Zr, neg_mul]

variable [IsFiniteMeasure ν]

/-- **L2. The LLC identity, log-averaged**: if `Z ν K` has learning pair `(λ, m)`, then for every
`t₀ > 0` there is `C` with
`|∫_{t₀}^{T} E_t[K] dt - (λ log T - (m-1) log log T)| ≤ C` for all large `T`. -/
theorem llc_log_average (hK : Measurable K) (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) {lam : ℝ} {m : ℕ}
    (h : HasLaplacePair (Z ν K) lam m) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ C T₀ : ℝ, ∀ T, T₀ ≤ T →
      |(∫ t in t₀..T, gibbsMean ν K t) -
        (lam * Real.log T - ((m : ℝ) - 1) * Real.log (Real.log T))| ≤ C := by
  have hm : 1 ≤ m := h.1
  have h' := (hasLaplacePair_Z_iff_hasLaplaceOrder hK hK0).mp h
  rw [Zr_eq_integral] at h'
  obtain ⟨-, c, C, N₀, hc, hC, hN₀, hb⟩ := h'
  -- `ν ≠ 0`, since `Z(N₀) > 0`.
  have hν : ν ≠ 0 := by
    rintro rfl
    have := (hb N₀ le_rfl).1
    simp only [Zr, integral_zero_measure] at this
    exact absurd this (not_le.mpr (mul_pos hc (rate_pos lam m hN₀)))
  refine ⟨|Real.log (Zr ν K t₀)| + |Real.log c| + |Real.log C|, N₀, fun T hT => ?_⟩
  have hT1 : 1 < T := lt_of_lt_of_le hN₀ hT
  have hr := rate_pos lam m hT1
  rw [integral_gibbsMean hK hK0 hν ht₀ (by linarith)]
  obtain ⟨hlo, hhi⟩ := hb T hT
  have hZ : 0 < Zr ν K T := lt_of_lt_of_le (mul_pos hc hr) hlo
  have l1 := Real.log_le_log (mul_pos hc hr) hlo
  have l2 := Real.log_le_log hZ hhi
  rw [Real.log_mul hc.ne' hr.ne'] at l1
  rw [Real.log_mul hC.ne' hr.ne'] at l2
  have lr := log_rate (lam := lam) hm hT1
  rw [abs_le]
  constructor <;>
  nlinarith [le_abs_self (Real.log (Zr ν K t₀)), neg_abs_le (Real.log (Zr ν K t₀)),
    le_abs_self (Real.log c), neg_abs_le (Real.log c), le_abs_self (Real.log C),
    neg_abs_le (Real.log C)]

/-- **L2, corollary**: `(1/log T) ∫_{t₀}^{T} E_t[K] dt → λ`. -/
theorem tendsto_llc_log_average (hK : Measurable K) (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) {lam : ℝ}
    {m : ℕ} (h : HasLaplacePair (Z ν K) lam m) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto (fun T => (∫ t in t₀..T, gibbsMean ν K t) / Real.log T) atTop (𝓝 lam) := by
  obtain ⟨C, T₀, hC⟩ := llc_log_average hK hK0 h ht₀
  set I : ℝ → ℝ := fun T => ∫ t in t₀..T, gibbsMean ν K t
  set R : ℝ → ℝ := fun T => I T - (lam * Real.log T - ((m : ℝ) - 1) * Real.log (Real.log T))
  have h1 : Tendsto (fun T => Real.log (Real.log T) / Real.log T) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have h2 : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := C)).div_atTop Real.tendsto_log_atTop)
    filter_upwards [eventually_ge_atTop T₀, eventually_gt_atTop 1] with T hT hT1
    have hl := Real.log_pos hT1
    rw [norm_div, Real.norm_of_nonneg hl.le]
    exact div_le_div_of_nonneg_right (hC T hT) hl.le
  have h3 := (tendsto_const_nhds (x := lam)).sub (h1.const_mul ((m : ℝ) - 1)) |>.add h2
  rw [mul_zero, sub_zero, add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with T hT1
  have hl := (Real.log_pos hT1).ne'
  simp only [R, I]
  field_simp
  ring

end SLT
