/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Newton.LowerTwo

/-!
# N2: the two-sided Newton theorem

`newtonTwoSided d : NewtonTwoSided d`. If `K` is comparable to `Σ_{α∈Γ} |w|^α` on `[0,1]^d` and
`t* > 0`, then `Z` has learning pair `(1/t*, m)` with `m = dim O + 1`.

Proof: for the monomial sum `M`, the sublevel volume `V(s) = vol{w ∈ [0,1]^d | M w ≤ s}` lies
between `H(log(|Γ|/s))` and `H(log(1/s))` (log coordinates). We have
`H(L) ≍ e^{-L/t*} L^{dim O}` (`Hfun_ge`, `Hfun_le`), so
`V(s) ≍ s^{1/t*} log(1/s)^{dim O}`, and `laplaceLower_of_volume` / `laplaceUpper_iff_volume` give
the pair. Comparability (`HasLaplacePair.of_comparable`) transfers it to `K`.
-/

@[expose] public section

namespace SLT.Newton

open MeasureTheory Set Filter Module

variable {d : ℕ}

theorem isFiniteMeasure_box : IsFiniteMeasure (volume.restrict (Icc (0 : Fin d → ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩

theorem V_box_eq (Γ : Finset (Fin d → ℝ)) (t : ℝ) :
    V (volume.restrict (Icc (0 : Fin d → ℝ) 1)) (monoSum Γ) t =
      volume (Icc (0 : Fin d → ℝ) 1 ∩ {w | monoSum Γ w ≤ t}) := by
  rw [V, Measure.restrict_apply (measurableSet_le (measurable_monoSum Γ) measurable_const),
    inter_comm]

theorem exp_neg_log_mul {a τ : ℝ} (ha : 0 < a) : Real.exp (-(Real.log a * τ)) = a ^ (-τ) := by
  rw [Real.rpow_def_of_pos ha]; ring_nf

/-- **N2 for the monomial sum**: `Z(N) = ∫_{[0,1]^d} e^{-N Σ|w|^α}` has pair `(1/t*, dim O + 1)`. -/
theorem hasLaplacePair_monoSum {Γ : Finset (Fin d → ℝ)} (hΓ : ∀ α ∈ Γ, ∀ i, 0 ≤ α i)
    (hd : 0 < newtonDist Γ) :
    HasLaplacePair (Z (volume.restrict (Icc (0 : Fin d → ℝ) 1)) (monoSum Γ)) (newtonDist Γ)⁻¹
      (newtonMult Γ) := by
  have := isFiniteMeasure_box (d := d)
  set τ := (newtonDist Γ)⁻¹ with hτdef
  have hτ : 0 < τ := inv_pos.mpr hd
  rw [newtonMult_eq]
  set k := optDim Γ with hkdef
  have hm : k + 1 - 1 = k := Nat.add_sub_cancel k 1
  have hG : (1 : ℝ) ≤ Γ.card := by
    exact_mod_cast Finset.card_pos.mpr (nonempty_of_newtonDist_pos hd)
  set G : ℝ := (Γ.card : ℝ)
  refine ⟨by omega, ?_, ?_⟩
  · -- lower bound
    obtain ⟨c, hc, hH⟩ := Hfun_ge hΓ hd
    refine laplaceLower_of_volume (measurable_monoSum Γ) (c := c * G ^ (-τ))
      (t₀ := min (G * Real.exp (-1)) 1) (by positivity) (lt_min (by positivity) one_pos)
      fun t ht ht₀ => ?_
    rw [hm, V_box_eq]
    have ht1 : t ≤ 1 := ht₀.trans (min_le_right _ _)
    have htG : t < G := by
      have := ht₀.trans (min_le_left _ _)
      have h1 : Real.exp (-1) < 1 := by simp
      nlinarith
    have hGt : 1 < G / t := by rw [one_lt_div ht]; exact htG
    have hL : 0 < Real.log (G / t) := Real.log_pos hGt
    refine le_trans ?_ ((hH _ hL).trans (volume_sublevel_ge Γ ht))
    refine ENNReal.ofReal_le_ofReal ?_
    rw [exp_neg_log_mul (by positivity), Real.div_rpow (by positivity) ht.le,
      Real.rpow_neg (by positivity), Real.rpow_neg ht.le]
    have hlog : Real.log (1 / t) ≤ Real.log (G / t) :=
      Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hG ht.le)
    have hlog0 : 0 ≤ Real.log (1 / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
    have hpow : Real.log (1 / t) ^ k ≤ Real.log (G / t) ^ k := pow_le_pow_left₀ hlog0 hlog k
    have hGτ : 0 < G ^ τ := Real.rpow_pos_of_pos (by linarith) _
    have htτ : 0 < t ^ τ := Real.rpow_pos_of_pos ht _
    rw [← hτdef, ← hkdef, div_inv_eq_mul]
    calc c * (G ^ τ)⁻¹ * t ^ τ * Real.log (1 / t) ^ k
        ≤ c * (G ^ τ)⁻¹ * t ^ τ * Real.log (G / t) ^ k := by gcongr
      _ = _ := by ring
  · -- upper bound
    obtain ⟨C₄, hC₄, hH⟩ := Hfun_le hd
    refine (laplaceUpper_iff_volume (measurable_monoSum Γ) (monoSum_nonneg Γ) hτ).mpr
      ⟨C₄, Real.exp (-1), Real.exp_pos _, fun t ht ht₀ => ?_⟩
    rw [hm, V_box_eq]
    have hL : 1 ≤ Real.log (1 / t) := by
      rw [one_div, Real.log_inv, le_neg]
      calc Real.log t ≤ Real.log (Real.exp (-1)) := Real.log_le_log ht ht₀
        _ = -1 := Real.log_exp _
    refine (volume_sublevel_le Γ t).trans ((hH _ hL).trans (ENNReal.ofReal_le_ofReal ?_))
    have e2 : (1 / t) ^ (-(newtonDist Γ)⁻¹) = t ^ (newtonDist Γ)⁻¹ := by
      rw [one_div, Real.inv_rpow ht.le, Real.rpow_neg (by positivity), inv_inv]
    rw [exp_neg_log_mul (by positivity), e2]

/-- **N2, the two-sided Newton theorem.** -/
theorem newtonTwoSided (d : ℕ) : NewtonTwoSided d := by
  intro Γ hΓ hd K hK c C hc hcomp
  have hM := hasLaplacePair_monoSum hΓ hd
  -- `C > 0`, by evaluating at `𝟙`
  have h1 : (fun _ : Fin d => (1 : ℝ)) ∈ Icc (0 : Fin d → ℝ) 1 :=
    ⟨fun _ => zero_le_one, fun _ => le_rfl⟩
  have hM1 : ∑ α ∈ Γ, monomial α (fun _ => 1) = Γ.card := by
    simp [monomial]
  have hG : (0 : ℝ) < Γ.card := by exact_mod_cast Finset.card_pos.mpr (nonempty_of_newtonDist_pos hd)
  have hC : 0 < C := by
    obtain ⟨h1', h2'⟩ := hcomp _ h1
    rw [hM1] at h1' h2'
    nlinarith
  refine hM.of_comparable hc hC ?_ ?_
  · exact (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun w hw => (hcomp w hw).1)
  · exact (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun w hw => (hcomp w hw).2)

end SLT.Newton
