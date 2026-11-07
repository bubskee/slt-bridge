/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Newton.Polytope
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Logarithmic coordinates (N2, change of variables)

`expNeg x = (e^{-x_i})_i` maps the orthant `x ≥ 0` bijectively onto `(0,1]^d`, with Jacobian
`e^{-⟨𝟙,x⟩}`. In these coordinates `|w|^α = e^{-⟨α,x⟩}`, so the sublevel volume of the monomial sum
on the box is squeezed between two values of
`H(L) = ∫_{x ≥ 0, ⟨α,x⟩ ≥ L ∀α} e^{-⟨𝟙,x⟩} dx`:

* `V(s) ≤ H(log(1/s))` (`volume_sublevel_le`),
* `V(s) ≥ H(log(|Γ|/s))` (`volume_sublevel_ge`).

Also here: `t*` is attained, so the set `O` of optimal weights is nonempty (`optWeights_nonempty`).
-/

@[expose] public section

namespace SLT.Newton

open MeasureTheory Set Matrix Metric Filter

variable {d : ℕ}

/-- The monomial sum `M(w) = Σ_{α∈Γ} |w|^α`. -/
noncomputable def monoSum (Γ : Finset (Fin d → ℝ)) (w : Fin d → ℝ) : ℝ :=
  ∑ α ∈ Γ, monomial α w

theorem monoSum_nonneg (Γ : Finset (Fin d → ℝ)) (w : Fin d → ℝ) : 0 ≤ monoSum Γ w :=
  Finset.sum_nonneg fun α _ => monomial_nonneg α w

theorem measurable_monoSum (Γ : Finset (Fin d → ℝ)) : Measurable (monoSum Γ) := by
  unfold monoSum monomial
  fun_prop

/-- `x ↦ (e^{-x_i})_i`. -/
noncomputable def expNeg (x : Fin d → ℝ) : Fin d → ℝ := fun i => Real.exp (-x i)

/-- Its derivative, `diag(-e^{-x_i})`. -/
noncomputable def expNegDeriv (x : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun i => (-Real.exp (-x i)) • ContinuousLinearMap.proj i

theorem hasFDerivAt_expNeg (x : Fin d → ℝ) : HasFDerivAt expNeg (expNegDeriv x) x := by
  refine hasFDerivAt_pi.2 fun i => ?_
  have := ((hasFDerivAt_apply i x).neg).exp
  convert this using 1
  · rfl
  · ext v; simp

theorem det_expNegDeriv (x : Fin d → ℝ) :
    (expNegDeriv x).det = ∏ i, -Real.exp (-x i) := by
  have : (expNegDeriv x : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) =
      Matrix.toLin' (Matrix.diagonal fun i => -Real.exp (-x i)) := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [expNegDeriv, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  rw [ContinuousLinearMap.det, this, LinearMap.det_toLin', Matrix.det_diagonal]

theorem abs_det_expNegDeriv (x : Fin d → ℝ) :
    |(expNegDeriv x).det| = Real.exp (-(ones ⬝ᵥ x)) := by
  rw [det_expNegDeriv, Finset.abs_prod, ones_dotProduct, neg_sum_eq, Real.exp_sum]
  · exact Finset.prod_congr rfl fun i _ => by rw [abs_neg, abs_of_pos (Real.exp_pos _)]
  where neg_sum_eq : -(∑ i, x i) = ∑ i, -x i := by rw [Finset.sum_neg_distrib]

theorem expNeg_injective : Function.Injective (expNeg : (Fin d → ℝ) → (Fin d → ℝ)) := by
  intro x y h
  funext i
  have := congrFun h i
  simp only [expNeg, Real.exp_eq_exp, neg_inj] at this
  exact this

/-- **Change of variables**: for measurable `S`, `vol(expNeg '' S) = ∫_S e^{-⟨𝟙,x⟩}`. -/
theorem volume_image_expNeg {S : Set (Fin d → ℝ)} (hS : MeasurableSet S) :
    volume (expNeg '' S) = ∫⁻ x in S, ENNReal.ofReal (Real.exp (-(ones ⬝ᵥ x))) := by
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume hS
    (fun x _ => (hasFDerivAt_expNeg x).hasFDerivWithinAt) expNeg_injective.injOn]
  simp only [abs_det_expNegDeriv]

theorem monomial_expNeg (α x : Fin d → ℝ) : monomial α (expNeg x) = Real.exp (-(α ⬝ᵥ x)) := by
  simp only [monomial, expNeg, abs_of_pos (Real.exp_pos _), ← Real.exp_mul, dotProduct,
    ← Real.exp_sum, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The cone `S_L = { x ≥ 0 | ⟨α,x⟩ ≥ L ∀ α ∈ Γ }`. -/
def logCone (Γ : Finset (Fin d → ℝ)) (L : ℝ) : Set (Fin d → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∀ α ∈ Γ, L ≤ α ⬝ᵥ x}

theorem measurableSet_logCone (Γ : Finset (Fin d → ℝ)) (L : ℝ) : MeasurableSet (logCone Γ L) := by
  have : logCone Γ L = (⋂ i, {x | 0 ≤ x i}) ∩ ⋂ α ∈ Γ, {x | L ≤ α ⬝ᵥ x} := by
    ext x; simp [logCone]
  rw [this]
  refine (MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i)).inter
    (MeasurableSet.biInter Γ.countable_toSet fun α _ => measurableSet_le measurable_const ?_)
  show Measurable fun x : Fin d → ℝ => ∑ i, α i * x i
  exact (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)).measurable

/-- `H(L) = ∫_{S_L} e^{-⟨𝟙,x⟩}`. -/
noncomputable def Hfun (Γ : Finset (Fin d → ℝ)) (L : ℝ) : ENNReal :=
  ∫⁻ x in logCone Γ L, ENNReal.ofReal (Real.exp (-(ones ⬝ᵥ x)))

/-- The box `[0,1]^d` and its sublevel volume for the monomial sum. -/
theorem volume_sublevel_le (Γ : Finset (Fin d → ℝ)) (s : ℝ) :
    volume (Icc (0 : Fin d → ℝ) 1 ∩ {w | monoSum Γ w ≤ s}) ≤ Hfun Γ (Real.log (1 / s)) := by
  rw [Hfun, ← volume_image_expNeg (measurableSet_logCone Γ _)]
  -- outside the boundary, every point of the box is `expNeg x` with `x ∈ S_{log(1/s)}`
  have hsub : Icc (0 : Fin d → ℝ) 1 ∩ {w | monoSum Γ w ≤ s} ⊆
      expNeg '' logCone Γ (Real.log (1 / s)) ∪ ⋃ i, {w : Fin d → ℝ | w i = 0} := by
    rintro w ⟨⟨hw0, hw1⟩, hws⟩
    by_cases hz : ∃ i, w i = 0
    · obtain ⟨i, hi⟩ := hz
      exact Or.inr (mem_iUnion.mpr ⟨i, hi⟩)
    push Not at hz
    have hpos : ∀ i, 0 < w i := fun i => lt_of_le_of_ne (hw0 i) (Ne.symm (hz i))
    refine Or.inl ⟨fun i => -Real.log (w i), ⟨fun i => ?_, fun α hα => ?_⟩, ?_⟩
    · exact neg_nonneg.mpr (Real.log_nonpos (hw0 i) (hw1 i))
    · have hx : expNeg (fun i => -Real.log (w i)) = w := by
        funext i; simp [expNeg, Real.exp_log (hpos i)]
      have hle : monomial α w ≤ s :=
        (Finset.single_le_sum (fun β _ => monomial_nonneg β w) hα).trans hws
      rw [← hx, monomial_expNeg] at hle
      have := Real.log_le_log (Real.exp_pos _) hle
      rw [Real.log_exp] at this
      rw [one_div, Real.log_inv]
      linarith
    · funext i; simp [expNeg, Real.exp_log (hpos i)]
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hnull : volume (⋃ i, {w : Fin d → ℝ | w i = 0}) = 0 := by
    refine measure_iUnion_null fun i => ?_
    have : {w : Fin d → ℝ | w i = 0} = (LinearMap.ker (LinearMap.proj i : (Fin d → ℝ) →ₗ[ℝ] ℝ) :
        Set (Fin d → ℝ)) := by ext w; simp
    rw [this]
    refine Measure.addHaar_submodule volume _ fun h => ?_
    have := congrArg (Pi.single i (1 : ℝ) ∈ ·) h
    simp at this
  rw [hnull, add_zero]

theorem volume_sublevel_ge (Γ : Finset (Fin d → ℝ)) {s : ℝ} (hs : 0 < s) :
    Hfun Γ (Real.log (Γ.card / s)) ≤ volume (Icc (0 : Fin d → ℝ) 1 ∩ {w | monoSum Γ w ≤ s}) := by
  rw [Hfun, ← volume_image_expNeg (measurableSet_logCone Γ _)]
  refine measure_mono ?_
  rintro _ ⟨x, ⟨hx0, hxα⟩, rfl⟩
  refine ⟨⟨fun i => (Real.exp_pos _).le, fun i => ?_⟩, ?_⟩
  · simp only [expNeg, Pi.one_apply, Real.exp_le_one_iff, neg_nonpos]; exact hx0 i
  · show monoSum Γ (expNeg x) ≤ s
    rcases Γ.eq_empty_or_nonempty with rfl | hne
    · simp [monoSum, hs.le]
    have hc : (0 : ℝ) < Γ.card := by exact_mod_cast Finset.card_pos.mpr hne
    have hterm : ∀ α ∈ Γ, monomial α (expNeg x) ≤ s / Γ.card := fun α hα => by
      rw [monomial_expNeg]
      have h := hxα α hα
      calc Real.exp (-(α ⬝ᵥ x)) ≤ Real.exp (-Real.log (Γ.card / s)) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = s / Γ.card := by
            rw [Real.exp_neg, Real.exp_log (div_pos hc hs), inv_div]
    calc monoSum Γ (expNeg x) ≤ ∑ _α ∈ Γ, s / Γ.card := Finset.sum_le_sum hterm
      _ = s := by rw [Finset.sum_const, nsmul_eq_mul]; field_simp

/-! ### `t*` is attained -/

/-- The standard simplex. -/
def simplex (d : ℕ) : Set (Fin d → ℝ) := {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i = 1}

theorem isCompact_simplex : IsCompact (simplex d) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have : simplex d = (⋂ i, {u : Fin d → ℝ | 0 ≤ u i}) ∩ {u | ∑ i, u i = 1} := by
      ext u; simp [simplex]
    rw [this]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  · refine (isBounded_iff_forall_norm_le).mpr ⟨1, fun u ⟨hu0, hu1⟩ => ?_⟩
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    rw [Real.norm_of_nonneg (hu0 i), ← hu1]
    exact Finset.single_le_sum (fun j _ => hu0 j) (Finset.mem_univ i)

/-- **`t*` is attained**: `O` is nonempty when `t* > 0`. -/
theorem optWeights_nonempty {Γ : Finset (Fin d → ℝ)} (hd : 0 < newtonDist Γ) :
    (optWeights Γ).Nonempty := by
  have hne := nonempty_of_newtonDist_pos hd
  -- the simplex is nonempty since some certificate exists
  have hcert : {t | ∃ u, IsNewtonCert Γ t u}.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [newtonDist, h, Real.sSup_empty] at hd
    exact lt_irrefl _ hd
  obtain ⟨t₀, u₀, hu₀⟩ := hcert
  set φ : (Fin d → ℝ) → ℝ := fun u => Γ.inf' hne fun α => α ⬝ᵥ u
  have hφc : Continuous φ := by
    refine Continuous.finset_inf'_apply (f := fun (α : Fin d → ℝ) (u : Fin d → ℝ) => α ⬝ᵥ u) hne
      fun α _ => ?_
    show Continuous fun u : Fin d → ℝ => ∑ i, α i * u i
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
  obtain ⟨u, hu, hmax⟩ := isCompact_simplex.exists_isMaxOn ⟨u₀, hu₀.1, hu₀.2.1⟩ hφc.continuousOn
  have hφ : ∀ α ∈ Γ, φ u ≤ α ⬝ᵥ u := fun α hα => Finset.inf'_le _ hα
  have hcu : IsNewtonCert Γ (φ u) u := ⟨hu.1, hu.2, fun α hα => by
    simpa [dotProduct] using hφ α hα⟩
  have hle : newtonDist Γ ≤ φ u := by
    refine csSup_le ⟨t₀, u₀, hu₀⟩ fun t ⟨u', hu'⟩ => ?_
    have h1 : t ≤ φ u' := Finset.le_inf' _ _ fun α hα => by simpa [dotProduct] using hu'.2.2 α hα
    exact h1.trans (hmax ⟨hu'.1, hu'.2.1⟩)
  exact ⟨u, hcu.mono hle⟩

end SLT.Newton
