/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
import Zoo.ResidualNetwork
import Zoo.VectorShear
import SLT.LLC.Identity

/-!
# Zoo: the LLC identity for the certified examples (brief 01, stage L3)

The log-averaged LLC identity `SLT.llc_log_average` / `SLT.tendsto_llc_log_average`, applied to
the zoo's certified learning pairs:

* scalar residual networks: `(1/log T) ∫_{t₀}^{T} E_t[K] dt → λ` with `λ` the paper's global
  learning coefficient, and the `O(1)` form with the multiplicity in the `log log T` term;
  worked instance: cubic depth 6, three active blocks, limit `2`;
* the vector shear network, position one: **unconditional**, limit `4`, and
  `∫_{t₀}^{T} E_t[K] dt = 4 log T - 4 log log T + O(1)` (multiplicity `5`);
* the full position table: **conditional on `ThmK`/`ThmN`**, as in the source. All four positions
  have log-averaged LLC `4`; position one differs from the others in the `log log T` term
  (`-4 log log T` against `0`).

As in `SLT.LLC.Identity`, these are *population, deterministic* statements about the exact loss and
the exact tempered posterior, not about the SGLD estimator (empirical loss, `β = 1/log n`).
-/

namespace SLT.Zoo

open MeasureTheory Filter Topology Real Set

/-! ### Scalar residual networks -/

section Residual

open ResidualSLT SLT.Zoo.ResidualNetwork

theorem networkTargetLoss_nonneg (μ : Measure ℝ) (r : ℕ) {L : ℕ} (t w : Fin L → ℝ) :
    0 ≤ networkTargetLoss μ r t w := by
  unfold networkTargetLoss
  exact integral_nonneg fun _ => sq_nonneg _

/-- **Scalar ResNet LLC identity, `O(1)` form**: under the paper's hypotheses, with
`(λ, m) = globalLearningPair r k (L-k)`,
`∫_{t₀}^{T} E_t[K] dt = λ log T - (m-1) log log T + O(1)`. -/
theorem residualNetwork_llc_log_average (μ : Measure ℝ) (r L k : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (t : Fin L → ℝ) (hk : activeCount (zeroExtend t) L = k)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : Measurable ρ) (hfinite : (∫⁻ w, (ρ w : ENNReal) ∂volume) < ⊤)
    (hprior : ∀ w, networkTargetLoss μ r t w = 0 → ContinuousAt ρ w ∧ 0 < ρ w)
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ C T₀ : ℝ, ∀ T, T₀ ≤ T →
      |(∫ s in t₀..T, gibbsMean (prior ρ) (networkTargetLoss μ r t) s) -
        ((globalLearningPair r k (L - k)).1 * Real.log T -
          (((globalLearningPair r k (L - k)).2 : ℝ) - 1) * Real.log (Real.log T))| ≤ C := by
  have : IsFiniteMeasure (prior ρ) := isFiniteMeasure_withDensity hfinite.ne
  exact llc_log_average (networkTargetLoss_continuous μ r L hr hL hμ t).measurable
    (Eventually.of_forall fun w => networkTargetLoss_nonneg μ r t w)
    (residualNetwork_learningPair μ r L k hr hL hμ t hk ρ hρ hfinite hprior) ht₀

/-- **Scalar ResNet LLC identity, limit form**: `(1/log T) ∫_{t₀}^{T} E_t[K] dt → λ`. -/
theorem residualNetwork_llc (μ : Measure ℝ) (r L k : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (t : Fin L → ℝ) (hk : activeCount (zeroExtend t) L = k)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : Measurable ρ) (hfinite : (∫⁻ w, (ρ w : ENNReal) ∂volume) < ⊤)
    (hprior : ∀ w, networkTargetLoss μ r t w = 0 → ContinuousAt ρ w ∧ 0 < ρ w)
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto (fun T => (∫ s in t₀..T, gibbsMean (prior ρ) (networkTargetLoss μ r t) s) /
      Real.log T) atTop (𝓝 (globalLearningPair r k (L - k)).1) := by
  have : IsFiniteMeasure (prior ρ) := isFiniteMeasure_withDensity hfinite.ne
  exact tendsto_llc_log_average (networkTargetLoss_continuous μ r L hr hL hμ t).measurable
    (Eventually.of_forall fun w => networkTargetLoss_nonneg μ r t w)
    (residualNetwork_learningPair μ r L k hr hL hμ t hk ρ hρ hfinite hprior) ht₀

/-- Worked instance: cubic, depth 6, three active blocks. The log-averaged LLC is `2`. -/
theorem cubic_depth6_three_active_llc {μ : Measure ℝ} {t : Fin 6 → ℝ}
    {ρ : (Fin 6 → ℝ) → NNReal} (h : UnifiedNetworkCertificate μ 3 6 3 t ρ)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures 3 6))
    (hfinite : (∫⁻ w, (ρ w : ENNReal) ∂volume) < ⊤) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto (fun T => (∫ s in t₀..T, gibbsMean (prior ρ) (networkTargetLoss μ 3 t) s) /
      Real.log T) atTop (𝓝 2) := by
  have : IsFiniteMeasure (prior ρ) := isFiniteMeasure_withDensity hfinite.ne
  exact tendsto_llc_log_average (networkTargetLoss_continuous μ 3 6 (by norm_num) (by norm_num) hμ t
    |>.measurable) (Eventually.of_forall fun w => networkTargetLoss_nonneg μ 3 t w)
    (cubic_depth6_three_active h) ht₀

end Residual

/-! ### The vector shear network -/

section Vector

open VectorSLT

theorem continuous_tri (i : ℕ) : Continuous fun v : ℝ × ℝ × ℝ => tri v i := by
  rcases i with _ | _ | i <;> simp only [tri] <;> fun_prop

theorem continuous_weights (i : ℕ) : Continuous fun θ : Raw16 => weights θ i := by
  rcases i with _ | i
  · simp only [weights]
    refine continuous_pi fun a => continuous_pi fun b => ?_
    fin_cases a <;> fin_cases b <;> simp <;> fun_prop
  · simp only [weights]
    refine continuous_pi fun a => continuous_pi fun b => ?_
    fin_cases a <;> fin_cases b <;> simp <;> exact (continuous_tri i).comp (by fun_prop)

theorem continuous_layer :
    Continuous fun q : Matrix (Fin 2) (Fin 2) ℝ × (Fin 2 → ℝ) => layer q.1 q.2 := by
  unfold layer
  exact continuous_snd.add ((continuous_fst.matrix_mulVec continuous_snd).pow 3)

/-- The network is jointly continuous in the raw weights and the input. -/
theorem continuous_net : Continuous fun p : Raw16 × (Fin 2 → ℝ) => net p.1 p.2 := by
  have step : ∀ n, Continuous fun p : Raw16 × (Fin 2 → ℝ) => prefixNet (weights p.1) n p.2 := by
    intro n
    induction n with
    | zero => simpa using continuous_snd
    | succ n ih =>
      simp only [prefixNet, Function.comp_apply]
      exact continuous_layer.comp (((continuous_weights n).comp continuous_fst).prodMk ih)
  exact step 4

/-- The population loss is measurable in the raw weights (it is a parametric integral of a
jointly continuous integrand). -/
theorem measurable_popLossA (μ : Measure (Fin 2 → ℝ)) [SFinite μ]
    (A : Matrix (Fin 2) (Fin 2) ℝ) : Measurable (popLossA μ A) := by
  have hc : Continuous fun p : Raw16 × (Fin 2 → ℝ) =>
      ∑ k, (net p.1 p.2 k - layer A p.2 k) ^ 2 := by
    refine continuous_finsetSum _ fun k _ => ?_
    have h1 := (continuous_apply k).comp continuous_net
    have h2 : Continuous fun p : Raw16 × (Fin 2 → ℝ) => layer A p.2 k :=
      (continuous_apply k).comp (continuous_layer.comp
        ((continuous_const : Continuous fun _ : Raw16 × (Fin 2 → ℝ) => A).prodMk continuous_snd))
    exact (h1.sub h2).pow 2
  exact (hc.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

/-- The localised prior at position `p`: `φ(θ) χ(θ - θ_p) dθ`. -/
noncomputable def posPrior (A : Matrix (Fin 2) (Fin 2) ℝ) (φ χ : Raw16 → ENNReal) (p : Fin 4) :
    Measure Raw16 :=
  volume.withDensity fun θ => φ θ * χ (θ - basePos A p)

/-- The source's localised partition function is the core's `Z` for the localised prior. -/
theorem Zpos_eq_Z {μ : Measure (Fin 2 → ℝ)} [SFinite μ] {A : Matrix (Fin 2) (Fin 2) ℝ}
    {φ χ : Raw16 → ENNReal} (hφm : Measurable φ) (hχm : Measurable χ) (p : Fin 4) :
    Zpos μ A φ χ p = SLT.Z (posPrior A φ χ p) (popLossA μ A) := by
  have hd : Measurable fun θ : Raw16 => φ θ * χ (θ - basePos A p) :=
    hφm.mul (hχm.comp (measurable_id.sub_const _))
  have hK := measurable_popLossA μ A
  funext N
  rw [SLT.Z, posPrior, lintegral_withDensity_eq_lintegral_mul _ hd (by fun_prop)]
  simp only [Zpos, Pi.mul_apply]
  exact lintegral_congr fun θ => mul_comm _ _

/-- With a bounded prior and a cutoff supported in the `r`-ball, the localised prior is finite. -/
theorem isFiniteMeasure_posPrior {A : Matrix (Fin 2) (Fin 2) ℝ} {φ χ : Raw16 → ENNReal}
    {π₁ r : ℝ} (hφ : ∀ θ, φ θ ≤ ENNReal.ofReal π₁) (hχ : ∀ θ, χ θ ≤ 1)
    (hχs : ∀ θ, r < ‖θ‖ → χ θ = 0) (p : Fin 4) : IsFiniteMeasure (posPrior A φ χ p) := by
  refine isFiniteMeasure_withDensity (ne_top_of_le_ne_top ?_ (lintegral_mono (g :=
    (Metric.closedBall (basePos A p) r).indicator fun _ => ENNReal.ofReal π₁) fun θ => ?_))
  · rw [lintegral_indicator_const Metric.isClosed_closedBall.measurableSet]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
  · by_cases hθ : θ ∈ Metric.closedBall (basePos A p) r
    · rw [indicator_of_mem hθ]
      calc φ θ * χ (θ - basePos A p) ≤ ENNReal.ofReal π₁ * 1 := mul_le_mul' (hφ θ) (hχ _)
        _ = _ := mul_one _
    · rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hθ
      rw [hχs _ hθ, mul_zero]
      exact bot_le

/-- **Vector shear, position one, LLC identity (unconditional)**: under the hypotheses of
`position_one_pair`, plus measurability of `φ` and `χ`, the log-averaged LLC of the localised
tempered posterior at position one satisfies
`∫_{t₀}^{T} E_t[K] dt = 4 log T - 4 log log T + O(1)`, hence tends to `4` after dividing by
`log T`. -/
theorem position_one_llc {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ᶠ θ in 𝓝 (basePos A 0), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      Measurable φ → Measurable χ → ∀ {t₀ : ℝ}, 0 < t₀ →
      (∃ C T₀ : ℝ, ∀ T, T₀ ≤ T →
        |(∫ s in t₀..T, gibbsMean (posPrior A φ χ 0) (popLossA μ A) s) -
          (4 * Real.log T - 4 * Real.log (Real.log T))| ≤ C) ∧
      Tendsto (fun T => (∫ s in t₀..T, gibbsMean (posPrior A φ χ 0) (popLossA μ A) s) /
        Real.log T) atTop (𝓝 4) := by
  obtain ⟨r, hr, h⟩ := VectorShear.position_one_pair hA
  refine ⟨r, hr, ?_⟩
  intro μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ φ₀ χ₀ π₁ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs hφm hχm t₀ ht₀
  have hp := h μ hmom hlh hμ₀ hμ φ χ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs
  rw [Zpos_eq_Z hφm hχm] at hp
  have := isFiniteMeasure_posPrior (A := A) hφ hχ hχs 0
  have hKm := measurable_popLossA μ A
  have hK0 : ∀ᵐ θ ∂(posPrior A φ χ 0), 0 ≤ popLossA μ A θ :=
    Eventually.of_forall fun θ => popLossA_nonneg μ A θ
  refine ⟨?_, tendsto_llc_log_average hKm hK0 hp ht₀⟩
  obtain ⟨C, T₀, hC⟩ := llc_log_average hKm hK0 hp ht₀
  exact ⟨C, T₀, fun T hT => by have := hC T hT; norm_num at this ⊢; linarith [this]⟩

/-- **Vector shear position table, LLC form (conditional on `ThmK`/`ThmN`)**: all four positions
have log-averaged LLC `4`; position one carries `-4 log log T` in the second-order term, positions
two to four carry none. -/
theorem mainTheorem_shear_llc {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ p : Fin 4, ∀ᶠ θ in 𝓝 (basePos A p), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ThmK μ A φ χ → ThmN μ A φ χ →
      Measurable φ → Measurable χ → ∀ {t₀ : ℝ}, 0 < t₀ →
      (∀ p : Fin 4, Tendsto (fun T =>
        (∫ s in t₀..T, gibbsMean (posPrior A φ χ p) (popLossA μ A) s) / Real.log T)
        atTop (𝓝 4)) ∧
      (∃ C T₀ : ℝ, ∀ T, T₀ ≤ T →
        |(∫ s in t₀..T, gibbsMean (posPrior A φ χ 0) (popLossA μ A) s) -
          (4 * Real.log T - 4 * Real.log (Real.log T))| ≤ C) ∧
      (∀ p : Fin 4, p ≠ 0 → ∃ C T₀ : ℝ, ∀ T, T₀ ≤ T →
        |(∫ s in t₀..T, gibbsMean (posPrior A φ χ p) (popLossA μ A) s) - 4 * Real.log T| ≤ C) := by
  obtain ⟨r, hr, h⟩ := VectorShear.mainTheorem_shear_core hA
  refine ⟨r, hr, ?_⟩
  intro μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ φ₀ χ₀ π₁ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs hK hN hφm hχm
    t₀ ht₀
  obtain ⟨h0, h1, h2, h3⟩ := h μ hmom hlh hμ₀ hμ φ χ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs hK hN
  have hKm := measurable_popLossA μ A
  have hK0 : ∀ p, ∀ᵐ θ ∂(posPrior A φ χ p), 0 ≤ popLossA μ A θ := fun _ =>
    Eventually.of_forall fun θ => popLossA_nonneg μ A θ
  have hfin := fun p => isFiniteMeasure_posPrior (A := A) hφ hχ hχs p
  have hpair : ∀ p : Fin 4, ∃ m : ℕ, (p = 0 → m = 5) ∧ (p ≠ 0 → m = 1) ∧
      HasLaplacePair (SLT.Z (posPrior A φ χ p) (popLossA μ A)) 4 m := by
    intro p
    fin_cases p
    · exact ⟨5, fun _ => rfl, fun h => absurd rfl h, by rw [← Zpos_eq_Z hφm hχm]; exact h0⟩
    · exact ⟨1, fun h => absurd h (by decide), fun _ => rfl, by rw [← Zpos_eq_Z hφm hχm]; exact h1⟩
    · exact ⟨1, fun h => absurd h (by decide), fun _ => rfl, by rw [← Zpos_eq_Z hφm hχm]; exact h2⟩
    · exact ⟨1, fun h => absurd h (by decide), fun _ => rfl, by rw [← Zpos_eq_Z hφm hχm]; exact h3⟩
  refine ⟨fun p => ?_, ?_, fun p hp => ?_⟩
  · obtain ⟨m, -, -, hm⟩ := hpair p
    have := hfin p
    exact tendsto_llc_log_average hKm (hK0 p) hm ht₀
  · obtain ⟨m, hm5, -, hm⟩ := hpair 0
    obtain rfl := hm5 rfl
    have := hfin 0
    obtain ⟨C, T₀, hC⟩ := llc_log_average hKm (hK0 0) hm ht₀
    exact ⟨C, T₀, fun T hT => by have := hC T hT; norm_num at this ⊢; linarith [this]⟩
  · obtain ⟨m, -, hm1, hm⟩ := hpair p
    obtain rfl := hm1 hp
    have := hfin p
    obtain ⟨C, T₀, hC⟩ := llc_log_average hKm (hK0 p) hm ht₀
    exact ⟨C, T₀, fun T hT => by have := hC T hT; norm_num at this ⊢; linarith [this]⟩

end Vector

end SLT.Zoo
