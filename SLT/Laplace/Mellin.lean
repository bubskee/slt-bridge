/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Laplace.Integral
public import SLT.NormalCrossing.Step

/-!
# The Mellin threshold: `λ` is an integrability exponent

For a finite measure `ν` and a loss `K > 0` a.e., the real Mellin identity is

  `∫₀^∞ t^{s-1} Z(t) dt = Γ(s) ∫ K^{-s} dν`   (`mellin_Z`, Tonelli; both sides in `ℝ≥0∞`).

So if `Z` has the pair `(λ, m)`, then for every `s > 0`

  `∫ K^{-s} dν < ∞  ↔  s < λ`   (`lintegral_rpow_neg_lt_top_iff`).

At `s = λ` the integral diverges for every `m ≥ 1`. This is the real-variable half of the
zeta-function picture: `λ` is the abscissa of convergence of `ζ(z) = ∫ K^z dν` at `z = -s`. It is
also the analytic log-canonical threshold: for `K = f²`, `λ = lct(f)/2`.

The real-valued form, with integrability instead of `ℝ≥0∞`, is
`ResidualSLT.inversePower_integrable_iff_of_laplace_order` in the scalar library.
-/

@[expose] public section

namespace SLT

open MeasureTheory Filter Real Set Asymptotics
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {ν : Measure α} {K : α → ℝ} {lam s : ℝ} {m : ℕ}

/-- `∫₀^∞ t^{s-1} e^{-a t} dt = Γ(s) a^{-s}` for `a, s > 0`, in `ℝ≥0∞`. -/
theorem lintegral_rpow_mul_exp_neg {a : ℝ} (ha : 0 < a) (hs : 0 < s) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (s - 1)) * ENNReal.ofReal (Real.exp (-(t * a))) =
      ENNReal.ofReal (Real.Gamma s) * ENNReal.ofReal (a ^ (-s)) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-(a * t))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s - 1) (p := 1) (b := a)
      (by linarith) one_pos ha
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
  calc ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (s - 1)) * ENNReal.ofReal (Real.exp (-(t * a)))
      = ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (s - 1) * Real.exp (-(a * t))) :=
        setLIntegral_congr_fun measurableSet_Ioi fun t ht => by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt ht) _), mul_comm t a]
    _ = ENNReal.ofReal (∫ t in Ioi 0, t ^ (s - 1) * Real.exp (-(a * t))) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le
    _ = _ := by
        rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs ha, one_div, Real.inv_rpow ha.le,
          ← Real.rpow_neg ha.le, mul_comm, ENNReal.ofReal_mul (Real.Gamma_pos_of_pos hs).le]

/-- **The Mellin identity** `∫₀^∞ t^{s-1} Z(t) dt = Γ(s) ∫ K^{-s} dν`. -/
theorem mellin_Z [SFinite ν] (hK : Measurable K) (hKpos : ∀ᵐ x ∂ν, 0 < K x) (hs : 0 < s) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (s - 1)) * Z ν K t =
      ENNReal.ofReal (Real.Gamma s) * ∫⁻ x, ENNReal.ofReal (K x ^ (-s)) ∂ν := by
  unfold Z
  simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap (by fun_prop)]
  refine lintegral_congr_ae ?_
  filter_upwards [hKpos] with x hx
  exact lintegral_rpow_mul_exp_neg hx hs

theorem Z_le_measure_univ (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) {N : ℝ} (hN : 0 ≤ N) : Z ν K N ≤ ν univ := by
  calc Z ν K N ≤ ∫⁻ _, 1 ∂ν := lintegral_mono_ae (hK0.mono fun x hx => by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (by nlinarith)))
    _ = ν univ := by rw [lintegral_const, one_mul]

/-- The `t → 0` part of the Mellin integral is finite. -/
theorem mellin_Z_Ioc_lt_top [IsFiniteMeasure ν] (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) (hs : 0 < s) {T : ℝ}
    (hT : 0 ≤ T) : ∫⁻ t in Ioc 0 T, ENNReal.ofReal (t ^ (s - 1)) * Z ν K t < ⊤ := by
  calc ∫⁻ t in Ioc 0 T, ENNReal.ofReal (t ^ (s - 1)) * Z ν K t
      ≤ ∫⁻ t in Ioc 0 T, ENNReal.ofReal (t ^ (s - 1)) * ν univ :=
        setLIntegral_mono' measurableSet_Ioc fun t ht => by
          gcongr; exact Z_le_measure_univ hK0 (le_of_lt ht.1)
    _ = ENNReal.ofReal (T ^ (s - 1 + 1) / (s - 1 + 1)) * ν univ := by
        rw [lintegral_mul_const _ (by fun_prop), NC.lintegral_Ioc_zero_rpow hT (by linarith)]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν univ)

/-- A nonnegative measurable function on `Ioi T` with finite `∫⁻ ofReal` is integrable there. -/
theorem integrableOn_of_lintegral_lt_top {f : ℝ → ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hf : Measurable f) (h0 : ∀ t ∈ S, 0 ≤ f t)
    (h : ∫⁻ t in S, ENNReal.ofReal (f t) < ⊤) : IntegrableOn f S :=
  ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    ((ae_restrict_iff' hS).mpr (Eventually.of_forall h0))).mpr h⟩

/-- **The Mellin threshold.** If `Z` has the pair `(λ, m)`, then `∫ K^{-s} dν < ∞ ↔ s < λ`
for every `s > 0`. -/
theorem lintegral_rpow_neg_lt_top_iff [IsFiniteMeasure ν] (hK : Measurable K)
    (hKpos : ∀ᵐ x ∂ν, 0 < K x) (hp : HasLaplacePair (Z ν K) lam m) (hs : 0 < s) :
    ∫⁻ x, ENNReal.ofReal (K x ^ (-s)) ∂ν < ⊤ ↔ s < lam := by
  have hK0 : ∀ᵐ x ∂ν, 0 ≤ K x := hKpos.mono fun _ h => h.le
  have hΓ : 0 < Real.Gamma s := Real.Gamma_pos_of_pos hs
  have hM := mellin_Z hK hKpos hs
  -- `∫ K^{-s} < ∞` iff the Mellin integral is finite
  have hiff : ∫⁻ x, ENNReal.ofReal (K x ^ (-s)) ∂ν < ⊤ ↔
      ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (s - 1)) * Z ν K t < ⊤ := by
    rw [hM]
    constructor
    · intro h; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h
    · intro h
      by_contra h'
      rw [not_lt, top_le_iff] at h'
      rw [h', ENNReal.mul_top (ENNReal.ofReal_pos.mpr hΓ).ne'] at h
      exact lt_irrefl _ h
  rw [hiff]
  obtain ⟨_, ⟨c, hc, hlo⟩, hup⟩ := hp
  obtain ⟨C, hC, hup⟩ := hup.exists_pos
  constructor
  · -- divergence for `s ≥ λ`
    intro hfin
    by_contra hge
    rw [not_lt] at hge
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hlo.and eventually_one_le_log)
    set T := max T₀ 1
    have hT : 0 < T := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hpt : ∀ t ∈ Ioi T, ENNReal.ofReal (c * t ^ (s - 1 - lam)) ≤
        ENNReal.ofReal (t ^ (s - 1)) * Z ν K t := by
      intro t ht
      have ht0 : 0 < t := hT.trans ht
      obtain ⟨h1, h2⟩ := hT₀ t ((le_max_left _ _).trans (le_of_lt ht))
      refine le_trans ?_ (mul_le_mul' le_rfl h1)
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _)]
      apply ENNReal.ofReal_le_ofReal
      have hr : t ^ (-lam) ≤ rate lam m t := by
        unfold rate
        calc t ^ (-lam) = t ^ (-lam) * 1 := (mul_one _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left (one_le_pow₀ h2) (Real.rpow_nonneg ht0.le _)
      calc c * t ^ (s - 1 - lam) = t ^ (s - 1) * (c * t ^ (-lam)) := by
            rw [show s - 1 - lam = (s - 1) + -lam by ring, Real.rpow_add ht0]; ring
        _ ≤ t ^ (s - 1) * (c * rate lam m t) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr hc.le)
              (Real.rpow_nonneg ht0.le _)
    have hfin' : ∫⁻ t in Ioi T, ENNReal.ofReal (c * t ^ (s - 1 - lam)) < ⊤ :=
      lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi hpt)
        (lt_of_le_of_lt (lintegral_mono_set (Ioi_subset_Ioi hT.le)) hfin)
    have hint := integrableOn_of_lintegral_lt_top measurableSet_Ioi (by fun_prop)
      (fun t ht => mul_nonneg hc.le (Real.rpow_nonneg (hT.trans ht).le _)) hfin'
    have hint2 : IntegrableOn (fun t : ℝ => t ^ (s - 1 - lam)) (Ioi T) :=
      IntegrableOn.congr_fun (Integrable.const_mul hint c⁻¹)
        (fun t _ => inv_mul_cancel_left₀ hc.ne' _) measurableSet_Ioi
    have := (integrableOn_Ioi_rpow_iff hT).mp hint2
    linarith
  · -- convergence for `s < λ`
    intro hlt
    set ε := (lam - s) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hlog := (log_pow_isLittleO_rpow (m - 1) hε0).bound one_pos
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hup.and (hlog.and eventually_one_le_log))
    set T := max T₀ 1
    have hT : 0 < T := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hsplit : Ioi (0 : ℝ) ⊆ Ioc 0 T ∪ Ioi T := fun t ht => by
      rcases le_or_gt t T with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr h
    have hpt : ∀ t ∈ Ioi T, ENNReal.ofReal (t ^ (s - 1)) * Z ν K t ≤
        ENNReal.ofReal (C * t ^ (s - 1 - lam + ε)) := by
      intro t ht
      have ht0 : 0 < t := hT.trans ht
      obtain ⟨h1, h2, h3⟩ := hT₀ t ((le_max_left _ _).trans (le_of_lt ht))
      rw [Real.norm_of_nonneg (pow_nonneg (by linarith) _),
        Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), one_mul] at h2
      refine (mul_le_mul' le_rfl h1).trans ?_
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _)]
      apply ENNReal.ofReal_le_ofReal
      unfold rate
      calc t ^ (s - 1) * (C * (t ^ (-lam) * Real.log t ^ (m - 1)))
          ≤ t ^ (s - 1) * (C * (t ^ (-lam) * t ^ ε)) := by
            gcongr
        _ = C * t ^ (s - 1 - lam + ε) := by
            rw [show s - 1 - lam + ε = (s - 1) + (-lam + ε) by ring, Real.rpow_add ht0,
              Real.rpow_add ht0]; ring
    have hint : IntegrableOn (fun t : ℝ => C * t ^ (s - 1 - lam + ε)) (Ioi T) :=
      (integrableOn_Ioi_rpow_of_lt (by rw [hε]; linarith) hT).const_mul C
    calc ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (s - 1)) * Z ν K t
        ≤ ∫⁻ t in Ioc 0 T ∪ Ioi T, ENNReal.ofReal (t ^ (s - 1)) * Z ν K t :=
          lintegral_mono_set hsplit
      _ ≤ (∫⁻ t in Ioc 0 T, ENNReal.ofReal (t ^ (s - 1)) * Z ν K t) +
            ∫⁻ t in Ioi T, ENNReal.ofReal (t ^ (s - 1)) * Z ν K t := lintegral_union_le _ _ _
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨mellin_Z_Ioc_lt_top hK0 hs hT.le,
          lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi hpt) hint.lintegral_lt_top⟩

end SLT
