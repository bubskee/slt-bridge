/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import ResidualSLT
public import SLT

/-!
# Zoo: positive homogeneous losses through the leading-map template (brief 03, T3 guardrail)

`ResidualSLT.positive_homogeneous_laplace_order` (residual-slt-in-a-haystack, `2865e70`) is the
scalar paper's pure-power Laplace order for a continuous loss `Q` that is positive away from `0` and
homogeneous of degree `2r`: `∫_{B(0,ε)} e^{-N Q} ≍ N^{-dim/(2r)}`.

`positive_homogeneous_laplace_order_template` re-derives it, both halves, through the core's T3
theorem (`SLT.Template.hasLaplacePair_of_leading`). It is the case of zero remainder (`G = G₀ = Q`,
`C = 0`). The statement is the source's, specialized to `E = Fin D → ℝ` with Lebesgue measure. (The
source allows any finite-dimensional normed space with any additive Haar measure. Its
`[Nontrivial E]` becomes `[Nontrivial (Fin D → ℝ)]`.)

`hasLaplacePair_of_homogeneous_add_remainder` is the T3 statement in the zoo's vocabulary. It
applies to the same kind of loss plus any remainder of weight `> 2r`, and is the form a new
architecture would check.
-/

@[expose] public section

namespace SLT.Zoo.TemplateLeading

open MeasureTheory Set Metric Filter SLT.Template
open scoped ENNReal

variable {D : ℕ}

/-- `Fin D → ℝ` is nontrivial only if `D ≥ 1`. -/
theorem one_le_of_nontrivial [Nontrivial (Fin D → ℝ)] : 1 ≤ D := by
  by_contra h
  have hD : D = 0 := by omega
  subst hD
  exact not_nontrivial (Fin 0 → ℝ) ‹_›

/-- The lintegral form of the ball integral of a continuous loss. -/
theorem ofReal_ball_integral {Q : (Fin D → ℝ) → ℝ} (hQ : Continuous Q) {ε N : ℝ} :
    ENNReal.ofReal (∫ w in ball (0 : Fin D → ℝ) ε, Real.exp (-N * Q w)) =
      ∫⁻ w in ball (0 : Fin D → ℝ) ε, ENNReal.ofReal (Real.exp (-(N * Q w))) := by
  rw [ofReal_integral_eq_lintegral_ofReal]
  · simp_rw [neg_mul]
  · exact ((by fun_prop : Continuous fun w => Real.exp (-N * Q w)).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall
  · exact Eventually.of_forall fun w => (Real.exp_pos _).le

/-- **`ResidualSLT.positive_homogeneous_laplace_order`, re-derived through the leading-map
template** (zero remainder), on `Fin D → ℝ` with Lebesgue measure. -/
theorem positive_homogeneous_laplace_order_template [Nontrivial (Fin D → ℝ)]
    {Q : (Fin D → ℝ) → ℝ} (r : ℕ) (hr : 0 < r) (hQ : Continuous Q)
    (hpos : ∀ w, w ≠ 0 → 0 < Q w) (hhom : ∀ (a : ℝ), 0 ≤ a → ∀ w, Q (a • w) = a ^ (2 * r) * Q w)
    (ε : ℝ) (hε : 0 < ε) :
    ResidualSLT.HasPowerLaplaceOrder ((Module.finrank ℝ (Fin D → ℝ) : ℝ) / (2 * r))
      (fun N => ∫ w in ball (0 : Fin D → ℝ) ε, Real.exp (-N * Q w)) := by
  have hD := one_le_of_nontrivial (D := D)
  rw [Module.finrank_fin_fun]
  obtain ⟨⟨c, hc, hshell⟩, -⟩ := shell_bounds_of_homogeneous hD hQ hpos
  have hrem : ∀ ε', HigherWeightRemainder Q Q r 0 ε' := fun ε' w _ => by simp
  have hCε : ∀ ε' : ℝ, 0 * ε' ≤ c / 2 := fun ε' => by linarith
  -- upper: the ball sits in `closedBall 0 ((2ε)/2)`
  obtain ⟨Cu, hCu⟩ := laplaceUpper_of_leading hD hQ.measurable (by omega : 1 ≤ r) hc le_rfl
    hhom hshell (hrem (2 * ε)) (hCε (2 * ε))
  -- lower: `closedBall 0 (ε/2)` sits in the ball
  obtain ⟨-, ⟨cl, hcl, hlow⟩, -⟩ := hasLaplacePair_of_leading hD hQ.measurable hQ
    (by omega : 1 ≤ r) hε hc le_rfl hhom hshell (hrem ε) (hCε ε)
  have hrate : ∀ N : ℝ, SLT.rate ((D : ℝ) / (2 * (r : ℝ))) 1 N = N ^ (-((D : ℝ) / (2 * r))) := by
    intro N; simp [SLT.rate]
  have hint_nn : ∀ N, 0 ≤ ∫ w in ball (0 : Fin D → ℝ) ε, Real.exp (-N * Q w) :=
    fun N => integral_nonneg fun w => (Real.exp_pos _).le
  constructor
  · refine ⟨cl, hcl, ?_⟩
    filter_upwards [hlow, eventually_ge_atTop 0] with N hN hN0
    rw [hrate] at hN
    have h1 : ∫⁻ w in closedBall (0 : Fin D → ℝ) (ε / 2), ENNReal.ofReal (Real.exp (-(N * Q w))) ≤
        ENNReal.ofReal (∫ w in ball (0 : Fin D → ℝ) ε, Real.exp (-N * Q w)) := by
      rw [ofReal_ball_integral hQ]
      exact lintegral_mono_set (closedBall_subset_ball (by linarith))
    exact (ENNReal.ofReal_le_ofReal_iff (hint_nn N)).mp (hN.trans h1)
  · refine ⟨max Cu 1, by positivity, ?_⟩
    filter_upwards [hCu, eventually_ge_atTop 0] with N hN hN0
    rw [hrate] at hN
    have h1 : ENNReal.ofReal (∫ w in ball (0 : Fin D → ℝ) ε, Real.exp (-N * Q w)) ≤
        ENNReal.ofReal (Cu * N ^ (-((D : ℝ) / (2 * r)))) := by
      rw [ofReal_ball_integral hQ]
      refine le_trans (lintegral_mono_set ?_) hN
      intro w hw
      rw [mem_closedBall_zero_iff]
      have := mem_ball_zero_iff.mp hw
      linarith
    have hpow : 0 ≤ N ^ (-((D : ℝ) / (2 * r))) := Real.rpow_nonneg hN0 _
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
      (h1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left Cu 1) hpow)))
    exact h2

/-- **The T3 interface in the zoo's vocabulary.** A loss `Q + R` with `Q` continuous, positive off
`0`, homogeneous of degree `2r`, and a remainder `|R w| ≤ C ‖w‖^{2r+1}` near `0`, has local learning
pair `(D/(2r), 1)` on every small enough ball. -/
theorem hasLaplacePair_of_homogeneous_add_remainder (hD : 1 ≤ D) {Q R : (Fin D → ℝ) → ℝ}
    (r : ℕ) (hr : 0 < r) (hQ : Continuous Q) (hR : Measurable R) (hpos : ∀ w, w ≠ 0 → 0 < Q w)
    (hhom : ∀ (a : ℝ), 0 ≤ a → ∀ w, Q (a • w) = a ^ (2 * r) * Q w) {C ε : ℝ} (hε : 0 < ε)
    (hC : 0 ≤ C) (hRb : ∀ w, ‖w‖ ≤ ε → |R w| ≤ C * ‖w‖ ^ (2 * r + 1)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε₀ →
      SLT.HasLaplacePair (fun N => ∫⁻ w in closedBall (0 : Fin D → ℝ) (δ / 2),
        ENNReal.ofReal (Real.exp (-(N * (Q w + R w))))) ((D : ℝ) / (2 * r)) 1 :=
  exists_hasLaplacePair_of_leading hD (hQ.measurable.add hR) hQ hpos (by omega) hε hC hhom
    (fun w hw => by simpa using hRb w hw)

end SLT.Zoo.TemplateLeading
