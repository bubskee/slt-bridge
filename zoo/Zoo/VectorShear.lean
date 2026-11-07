/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
import VectorSLT
import SLT

/-!
# Zoo: the vector cubic ResNet (*Rank, Shears, and Logarithmic Multiplicity…*)

The certified results of `vector-slt-lean` (commit `2d545cd`, which renamed its SLT layer to
`VectorSLT.SLT`), restated in the shared core's vocabulary.

* `ofVector`: the vector library's `VectorSLT.SLT.HasLaplacePair` together with `1 ≤ m` is the core
  pair. The core's `hasLaplacePair_iff_bounds` has the vector body verbatim, so this is checked by
  the kernel.
* `position_one_pair`: **unconditional**. Position one of the depth-four shear network has pair
  `(4, 5)`.
* `position_one_unique`: that pair is intrinsic.
* `mainTheorem_shear_core`, `mainTheorem_shear_gaussian_core`: the position table
  `(4,5), (4,1), (4,1), (4,1)`. The upper halves at positions two to four are **conditional** on the
  named hypotheses `ThmK` and `ThmN`, exactly as in the source.

Here `Zpos μ A φ χ p N = ∫ e^{-N K(θ)} φ(θ) χ(θ - θ_p) dθ` is the localised partition function at
the `p`-th base point, with `K = popLossA μ A` the population loss of the raw-weight network.
Everything here is a corollary; the mathematics is in `VectorSLT`. (`VectorSLT` is not written in
the `module` system, so this file is a plain, non-`module` file.)
-/

namespace SLT.Zoo.VectorShear

open MeasureTheory Filter Topology VectorSLT

/-- The vector library's pair predicate, with `1 ≤ m`, is the core's. -/
theorem ofVector {F : ℝ → ENNReal} {lam : ℝ} {m : ℕ} (h : VectorSLT.SLT.HasLaplacePair F lam m)
    (hm : 1 ≤ m) : SLT.HasLaplacePair F lam m :=
  SLT.hasLaplacePair_iff_bounds.mpr ⟨hm, h⟩

/-- A core pair is a pair for the vector library's predicate (forgetting `1 ≤ m`). -/
theorem toVector {F : ℝ → ENNReal} {lam : ℝ} {m : ℕ} (h : SLT.HasLaplacePair F lam m) :
    VectorSLT.SLT.HasLaplacePair F lam m :=
  (SLT.hasLaplacePair_iff_bounds.mp h).2

/-- (G6) **Position one, unconditionally**: for every shear target, every input law with finite
162nd moments and a density bounded below on a box, every bounded prior that is bounded below near
the first base point, and every admissible cutoff, `Z_{N,1}` has the learning pair `(4, 5)`. -/
theorem position_one_pair {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) :
    ∃ r : ℝ, 0 < r ∧ ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ],
      (∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ) →
      ∀ {lo hi : Fin 2 → ℝ}, (∀ i, lo i < hi i) → ∀ {μ₀ : ℝ}, 0 < μ₀ →
      ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ →
      ∀ (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ᶠ θ in 𝓝 (basePos A 0), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      SLT.HasLaplacePair (Zpos μ A φ χ 0) 4 5 := by
  obtain ⟨r, hr, h⟩ := ZN1_two_sided_moments hA
  refine ⟨r, hr, ?_⟩
  intro μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ φ₀ χ₀ π₁ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs
  obtain ⟨c, C, N₀, hc, hb⟩ := h μ hmom hlh hμ₀ hμ φ χ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs
  exact ofVector (hasLaplacePair_45 hc hb) (by norm_num)

/-- The position-one pair is intrinsic: any core pair of `Z_{N,1}` is `(4, 5)`. -/
theorem position_one_unique {μ : Measure (Fin 2 → ℝ)} {A : Matrix (Fin 2) (Fin 2) ℝ}
    {φ χ : Raw16 → ENNReal} (h : SLT.HasLaplacePair (Zpos μ A φ χ 0) 4 5) {lam : ℝ} {m : ℕ}
    (h' : SLT.HasLaplacePair (Zpos μ A φ χ 0) lam m) : lam = 4 ∧ m = 5 :=
  h'.unique h

/-- (G6) **Main theorem in core vocabulary**: the depth-four position table
`(4,5), (4,1), (4,1), (4,1)`, conditional on `ThmK` and `ThmN` (upper halves at positions 2–4). -/
theorem mainTheorem_shear_core {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) :
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
      SLT.HasLaplacePair (Zpos μ A φ χ 0) 4 5 ∧ SLT.HasLaplacePair (Zpos μ A φ χ 1) 4 1 ∧
        SLT.HasLaplacePair (Zpos μ A φ χ 2) 4 1 ∧ SLT.HasLaplacePair (Zpos μ A φ χ 3) 4 1 := by
  obtain ⟨r, hr, h⟩ := mainTheorem_shear hA
  refine ⟨r, hr, ?_⟩
  intro μ _ hmom lo hi hlh μ₀ hμ₀ hμ φ χ φ₀ χ₀ π₁ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs hK hN
  obtain ⟨h0, h1, h2, h3⟩ :=
    h μ hmom hlh hμ₀ hμ φ χ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs hK hN
  exact ⟨ofVector h0 (by norm_num), ofVector h1 le_rfl, ofVector h2 le_rfl, ofVector h3 le_rfl⟩

/-- (G6) **Positions are told apart by the multiplicity**: if position one has pair `(4,5)` and
position `p` has pair `(4,1)`, the two partition functions are different functions of `N`, by
uniqueness of the pair. The source's `mainTheorem_shear_ratio` proves the stronger
`Z_{N,1}/Z_{N,p} → ∞`. -/
theorem position_one_ne_position {μ : Measure (Fin 2 → ℝ)} {A : Matrix (Fin 2) (Fin 2) ℝ}
    {φ χ : Raw16 → ENNReal} (h0 : SLT.HasLaplacePair (Zpos μ A φ χ 0) 4 5) {p : Fin 4}
    (hp : SLT.HasLaplacePair (Zpos μ A φ χ p) 4 1) : Zpos μ A φ χ 0 ≠ Zpos μ A φ χ p := by
  intro he
  rw [he] at h0
  have := (h0.unique hp).2
  norm_num at this

/-- (G6) **Gaussian inputs**: the same table for the standard Gaussian input law. -/
theorem mainTheorem_shear_gaussian_core {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ShearTarget A) :
    ∃ r : ℝ, 0 < r ∧ ∀ (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ}, 0 < φ₀ → 0 < χ₀ →
      (∀ p : Fin 4, ∀ᶠ θ in 𝓝 (basePos A p), ENNReal.ofReal φ₀ ≤ φ θ) →
      (∀ᶠ θ in 𝓝 0, ENNReal.ofReal χ₀ ≤ χ θ) →
      0 ≤ π₁ → (∀ θ, φ θ ≤ ENNReal.ofReal π₁) →
      (∀ θ, χ θ ≤ 1) → (∀ θ, r < ‖θ‖ → χ θ = 0) →
      ThmK stdGauss2 A φ χ → ThmN stdGauss2 A φ χ →
      SLT.HasLaplacePair (Zpos stdGauss2 A φ χ 0) 4 5 ∧
        SLT.HasLaplacePair (Zpos stdGauss2 A φ χ 1) 4 1 ∧
        SLT.HasLaplacePair (Zpos stdGauss2 A φ χ 2) 4 1 ∧
        SLT.HasLaplacePair (Zpos stdGauss2 A φ χ 3) 4 1 := by
  obtain ⟨r, hr, h⟩ := mainTheorem_shear_gaussian hA
  refine ⟨r, hr, fun φ χ φ₀ χ₀ π₁ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs hK hN => ?_⟩
  obtain ⟨h0, h1, h2, h3⟩ := h φ χ hφ₀ hχ₀ hφl hχl hπ₁ hφ hχ hχs hK hN
  exact ⟨ofVector h0 (by norm_num), ofVector h1 le_rfl, ofVector h2 le_rfl, ofVector h3 le_rfl⟩

end SLT.Zoo.VectorShear
