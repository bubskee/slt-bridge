/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import ResidualSLT
public import SLT

/-!
# Zoo: scalar residual networks (*Residual SLT in a Haystack*)

The certified results of `bubskee/residual-slt-in-a-haystack` (Lean source at the paper's
reproducibility snapshot `2865e70`), restated in the shared core's vocabulary:
`SLT.HasLaplacePair (SLT.Z ν K) λ m` with `ν = volume.withDensity ρ` the raw-weight prior and
`K = networkTargetLoss μ r t` the population squared-error loss of the actual network.

* `hasLaplaceOrder_iff`: the scalar library's `HasLaplaceOrder` *is* the core's
  `SLT.HasLaplaceOrder` (`Iff.rfl`), so the adapter is checked by the kernel rather than by reading.
* `global_pair`, `residualNetwork_learningPair`: the paper's Theorem 3 (global pair), as a core pair.
* `global_pair_unique`: the pair is **intrinsic**. Any Laplace pair of this `Z` equals
  `globalLearningPair`. This is the core's uniqueness theorem applied to the paper.
* `local_pair`: the local arrangement certificates (Theorem 2) as core pairs on small balls.
* Worked instances: the cubic depth-6 target with 3 active blocks has pair `(2, 2)`; and in depth 5
  with one active block, two realizations of the same function have local pairs `(7/6, 2)` and
  `(7/6, 1)` (the paper's figure).

Everything here is a corollary. The mathematics is in `ResidualSLT`; this file only translates it.
-/

@[expose] public section

namespace SLT.Zoo.ResidualNetwork

open MeasureTheory Metric Set ResidualSLT

/-- The scalar library's two-sided Laplace predicate is, definitionally, the core's. -/
theorem hasLaplaceOrder_iff (ℓ : ℝ) (m : ℕ) (Z : ℝ → ℝ) :
    ResidualSLT.HasLaplaceOrder ℓ m Z ↔ SLT.HasLaplaceOrder ℓ m Z := Iff.rfl

/-- The raw-weight prior `ρ(w) dw`. -/
noncomputable abbrev prior {L : ℕ} (ρ : (Fin L → ℝ) → NNReal) : Measure (Fin L → ℝ) :=
  volume.withDensity fun w => (ρ w : ENNReal)

variable {μ : Measure ℝ} {r L k : ℕ} {t : Fin L → ℝ} {ρ : (Fin L → ℝ) → NNReal}

/-- **Global pair (Theorem 3) as a core pair.** -/
theorem global_pair (h : UnifiedNetworkCertificate μ r L k t ρ) :
    SLT.HasLaplacePair (SLT.Z (prior ρ) (networkTargetLoss μ r t))
      (globalLearningPair r k (L - k)).1 (globalLearningPair r k (L - k)).2 :=
  hasLaplacePair_Z_of_hasLaplaceOrder ((hasLaplaceOrder_iff _ _ _).mp h.global_laplace)

/-- **The global pair is intrinsic**: any Laplace pair of the network's `Z` is
`globalLearningPair r k (L-k)`. -/
theorem global_pair_unique (h : UnifiedNetworkCertificate μ r L k t ρ) {lam : ℝ} {m : ℕ}
    (h' : SLT.HasLaplacePair (SLT.Z (prior ρ) (networkTargetLoss μ r t)) lam m) :
    lam = (globalLearningPair r k (L - k)).1 ∧ m = (globalLearningPair r k (L - k)).2 :=
  h'.unique (global_pair h)

/-- **The scalar ResNet learning pair**, from the paper's hypotheses: degree `r ≥ 2`, depth
`L > 0`, a positive-definite feature Gram for the input law, a target with `k` active blocks, and
a finite prior that is continuous and positive on the zero set. -/
theorem residualNetwork_learningPair (μ : Measure ℝ) (r L k : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (t : Fin L → ℝ) (hk : activeCount (zeroExtend t) L = k)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : Measurable ρ) (hfinite : (∫⁻ w, (ρ w : ENNReal) ∂volume) < ⊤)
    (hprior : ∀ w, networkTargetLoss μ r t w = 0 → ContinuousAt ρ w ∧ 0 < ρ w) :
    SLT.HasLaplacePair (SLT.Z (prior ρ) (networkTargetLoss μ r t))
      (globalLearningPair r k (L - k)).1 (globalLearningPair r k (L - k)).2 :=
  global_pair (unified_residual_network_certificate μ r L k hr hL hμ t hk ρ hρ hfinite hprior)

/-- **Local pairs (Theorem 2) as core pairs**: a local certificate at `x` with pair `p` gives
`HasLaplacePair` for the prior restricted to every small ball around `x`. -/
theorem local_pair {x : Fin L → ℝ} {p : ℝ × ℕ} (h : LocalNetworkCertificate μ r t x ρ p) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      SLT.HasLaplacePair (SLT.Z ((prior ρ).restrict (ball x ε)) (networkTargetLoss μ r t))
        p.1 p.2 := by
  obtain ⟨ε₀, hε₀, -, hε⟩ := h
  exact ⟨ε₀, hε₀, fun ε hpos hle => hasLaplacePair_Z_of_hasLaplaceOrder
    ((hasLaplaceOrder_iff _ _ _).mp (hε ε hpos hle).2.2)⟩

/-! ### Worked instances -/

/-- Cubic network, depth 6, three active blocks: the learning pair is `(λ, m) = (2, 2)`. -/
theorem cubic_depth6_three_active {t : Fin 6 → ℝ} {ρ : (Fin 6 → ℝ) → NNReal} (h : UnifiedNetworkCertificate μ 3 6 3 t ρ) :
    SLT.HasLaplacePair (SLT.Z (prior ρ) (networkTargetLoss μ 3 t)) 2 2 := by
  have := global_pair h
  norm_num [globalLearningPair, identityLearningPair] at this
  exact this

/-- Depth-five cubic network with one active block: the realization `(0,1,0,0,0)` of the target
`(1,0,0,0,0)` has local pair `(7/6, 2)`. -/
theorem cubic_depth5_local_split13 {ρ : (Fin 5 → ℝ) → NNReal}
    (h : UnifiedNetworkCertificate μ 3 5 1 (![1, 0, 0, 0, 0] : Fin 5 → ℝ) ρ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      SLT.HasLaplacePair (SLT.Z ((prior ρ).restrict (ball (![0, 1, 0, 0, 0] : Fin 5 → ℝ) ε))
        (networkTargetLoss μ 3 (![1, 0, 0, 0, 0] : Fin 5 → ℝ))) (7 / 6) 2 := by
  have hz : networkTargetLoss μ 3 (![1, 0, 0, 0, 0] : Fin 5 → ℝ) ![0, 1, 0, 0, 0] = 0 := by
    rw [h.odd_fiber (by decide)]
    norm_num [activeWord, zeroExtend]
  have hd : arrangementDepth 1 ![1, 3] 1 le_rfl = 5 := by norm_num [arrangementDepth]
  have hc := h.local_at_arrangement ![0, 1, 0, 0, 0] hz ![1, 3] ![1]
    (by intro j; fin_cases j; norm_num) hd (by
      intro i
      rw [arrangement_one_center]
      fin_cases i <;> norm_num [Fin.cast])
  norm_num [arrangementLearningPair, identityLearningPair, Fin.sum_univ_succ] at hc
  exact local_pair hc

/-- Same target, same prior, realization `(0,0,1,0,0)`: the same exponent `7/6`, but
multiplicity `1`. -/
theorem cubic_depth5_local_split22 {ρ : (Fin 5 → ℝ) → NNReal}
    (h : UnifiedNetworkCertificate μ 3 5 1 (![1, 0, 0, 0, 0] : Fin 5 → ℝ) ρ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      SLT.HasLaplacePair (SLT.Z ((prior ρ).restrict (ball (![0, 0, 1, 0, 0] : Fin 5 → ℝ) ε))
        (networkTargetLoss μ 3 (![1, 0, 0, 0, 0] : Fin 5 → ℝ))) (7 / 6) 1 := by
  have hz : networkTargetLoss μ 3 (![1, 0, 0, 0, 0] : Fin 5 → ℝ) ![0, 0, 1, 0, 0] = 0 := by
    rw [h.odd_fiber (by decide)]
    norm_num [activeWord, zeroExtend]
  have hd : arrangementDepth 1 ![2, 2] 1 le_rfl = 5 := by norm_num [arrangementDepth]
  have hc := h.local_at_arrangement ![0, 0, 1, 0, 0] hz ![2, 2] ![1]
    (by intro j; fin_cases j; norm_num) hd (by
      intro i
      rw [arrangement_one_center]
      fin_cases i <;> norm_num [Fin.cast])
  norm_num [arrangementLearningPair, identityLearningPair, Fin.sum_univ_succ] at hc
  exact local_pair hc

end SLT.Zoo.ResidualNetwork
