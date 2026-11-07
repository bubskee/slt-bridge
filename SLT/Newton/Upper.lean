/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Newton.LogCoords
public import SLT.Newton.Tube

/-!
# The upper bound `H(L) ≲ e^{-L/t*} L^{dim O}` (N2)

* `finrank_dualSlab_zero_le`: the optimal face `P_0 ⊆ (1/t*)·O` has affine dimension `≤ dim O`;
* `volume_dualSlab_le`: `vol(P_η) ≤ C η^{d - dim O} (1+η)^{dim O}`, by the slab bound
  (`dualSlab_subset`) and the tube bound (`volume_thicken_le`) for small `η`, and a ball for
  large `η`;
* `Hfun_le`: summing over the shells `L/t* + j ≤ ⟨𝟙,x⟩ ≤ L/t* + j + 1` gives
  `H(L) ≤ C e^{-L/t*} L^{dim O}` for `L ≥ 1`.
-/

@[expose] public section

namespace SLT.Newton

open MeasureTheory Set Matrix Metric Filter Module
open scoped Pointwise

variable {d : ℕ}

/-- `dim O`, so that `newtonMult Γ = optDim Γ + 1`. -/
noncomputable abbrev optDim (Γ : Finset (Fin d → ℝ)) : ℕ :=
  finrank ℝ (affineSpan ℝ (optWeights Γ)).direction

/-- `newtonMult Γ = optDim Γ + 1`, by definition. -/
theorem newtonMult_eq (Γ : Finset (Fin d → ℝ)) : newtonMult Γ = optDim Γ + 1 := rfl

private theorem optDim_le (Γ : Finset (Fin d → ℝ)) : optDim Γ ≤ d := by
  have := Submodule.finrank_le (affineSpan ℝ (optWeights Γ)).direction
  rwa [Module.finrank_fin_fun] at this

private theorem dualSlab_zero_subset {Γ : Finset (Fin d → ℝ)} (hd : 0 < newtonDist Γ) :
    dualSlab Γ 0 ⊆ (fun u => (newtonDist Γ)⁻¹ • u) '' optWeights Γ := by
  intro u hu
  have hge := one_dot_ge hd hu.1
  have heq : ones ⬝ᵥ u = (newtonDist Γ)⁻¹ := le_antisymm (by simpa using hu.2) hge
  obtain ⟨⟨hu0, hu1⟩, -⟩ := hu
  refine ⟨newtonDist Γ • u, ⟨fun i => mul_nonneg hd.le (hu0 i), ?_, fun α hα => ?_⟩, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ← ones_dotProduct, heq]
    exact mul_inv_cancel₀ hd.ne'
  · have h := hu1 α hα
    have : ∑ i, α i * (newtonDist Γ • u) i = newtonDist Γ * (α ⬝ᵥ u) := by
      simp only [Pi.smul_apply, smul_eq_mul, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    exact le_mul_of_one_le_right hd.le h
  · simp only [smul_smul, inv_mul_cancel₀ hd.ne', one_smul]

private theorem finrank_dualSlab_zero_le {Γ : Finset (Fin d → ℝ)} (hd : 0 < newtonDist Γ) :
    finrank ℝ (affineSpan ℝ (dualSlab Γ 0)).direction ≤ optDim Γ := by
  set f : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) := (newtonDist Γ)⁻¹ • LinearMap.id
  have himg : (fun u => (newtonDist Γ)⁻¹ • u) '' optWeights Γ = f.toAffineMap '' optWeights Γ := rfl
  have h1 : affineSpan ℝ (dualSlab Γ 0) ≤ (affineSpan ℝ (optWeights Γ)).map f.toAffineMap := by
    rw [AffineSubspace.map_span, ← himg]
    exact affineSpan_mono ℝ (dualSlab_zero_subset hd)
  calc finrank ℝ (affineSpan ℝ (dualSlab Γ 0)).direction
      ≤ finrank ℝ ((affineSpan ℝ (optWeights Γ)).map f.toAffineMap).direction :=
        Submodule.finrank_mono (AffineSubspace.direction_le h1)
    _ ≤ optDim Γ := by
        rw [AffineSubspace.map_direction]
        exact Submodule.finrank_map_le _ _

/-- (N2 proof) **Slab volume**: `vol(P_η) ≤ C η^{d-k} (1+η)^k` with `k = dim O`. -/
private theorem volume_dualSlab_le {Γ : Finset (Fin d → ℝ)} (hd : 0 < newtonDist Γ) :
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ η : ℝ, 0 < η →
      volume (dualSlab Γ η) ≤
        ENNReal.ofReal (C₃ * η ^ (d - optDim Γ) * (1 + η) ^ optDim Γ) := by
  obtain ⟨g, hg, C, hC, hsub⟩ := dualSlab_subset hd
  obtain ⟨CT, hCT, htube⟩ := volume_thicken_le (isCompact_dualSlab Γ 0)
  have hkF := finrank_dualSlab_zero_le hd
  have hk := optDim_le Γ
  set k := optDim Γ
  set kF := finrank ℝ (affineSpan ℝ (dualSlab Γ 0)).direction
  set τ := (newtonDist Γ)⁻¹
  have hτ : 0 < τ := inv_pos.mpr hd
  set η₀ := min (g / 2) (1 / (C + 1))
  have hη₀ : 0 < η₀ := lt_min (by linarith) (by positivity)
  refine ⟨max (CT * (C + 1) ^ d) ((2 * (τ / η₀ + 1)) ^ d), le_max_of_le_left (by positivity),
    fun η hη => ?_⟩
  have h1η : 1 ≤ (1 + η) ^ k := one_le_pow₀ (by linarith)
  by_cases hsmall : η ≤ η₀
  · have hηg : η < g := lt_of_le_of_lt (hsmall.trans (min_le_left _ _)) (by linarith)
    have hr1 : (C + 1) * η ≤ 1 := by
      have : η ≤ 1 / (C + 1) := hsmall.trans (min_le_right _ _)
      rw [le_div_iff₀ (by linarith)] at this; linarith
    have hη1 : η ≤ 1 := by nlinarith
    calc volume (dualSlab Γ η)
        ≤ volume (dualSlab Γ 0 + closedBall (0 : Fin d → ℝ) ((C + 1) * η)) := by
          refine measure_mono ((hsub η hη.le hηg).trans (add_subset_add_left ?_))
          exact closedBall_subset_closedBall (by nlinarith)
      _ ≤ ENNReal.ofReal (CT * ((C + 1) * η) ^ (d - kF)) :=
          htube _ (by positivity) hr1
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_pow]
          have e1 : (C + 1) ^ (d - kF) ≤ (C + 1) ^ d :=
            pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
          have e2 : η ^ (d - kF) ≤ η ^ (d - k) := pow_le_pow_of_le_one hη.le hη1 (by omega)
          calc CT * ((C + 1) ^ (d - kF) * η ^ (d - kF))
              ≤ CT * ((C + 1) ^ d * η ^ (d - k)) := by gcongr
            _ = CT * (C + 1) ^ d * η ^ (d - k) * 1 := by ring
            _ ≤ max (CT * (C + 1) ^ d) ((2 * (τ / η₀ + 1)) ^ d) * η ^ (d - k) * (1 + η) ^ k := by
                gcongr; exact le_max_left _ _
  · push Not at hsmall
    have hball : dualSlab Γ η ⊆ closedBall (0 : Fin d → ℝ) (τ + η) := fun u hu => by
      rw [mem_closedBall, dist_zero_right]
      exact (dualSlab_isBounded Γ η u hu).trans (abs_of_pos (by linarith)).le
    calc volume (dualSlab Γ η) ≤ volume (closedBall (0 : Fin d → ℝ) (τ + η)) := measure_mono hball
      _ = ENNReal.ofReal ((2 * (τ + η)) ^ d) := by
          rw [Real.volume_pi_closedBall _ (by linarith), Fintype.card_fin]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hle : τ + η ≤ (τ / η₀ + 1) * η := by
            have : τ ≤ τ / η₀ * η := by
              rw [div_mul_eq_mul_div, le_div_iff₀ hη₀]; nlinarith
            linarith
          have hpow : η ^ d = η ^ (d - k) * η ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
          have hηk : η ^ k ≤ (1 + η) ^ k := pow_le_pow_left₀ hη.le (by linarith) _
          calc (2 * (τ + η)) ^ d ≤ (2 * ((τ / η₀ + 1) * η)) ^ d := by gcongr
            _ = (2 * (τ / η₀ + 1)) ^ d * (η ^ (d - k) * η ^ k) := by
                rw [← hpow, show 2 * ((τ / η₀ + 1) * η) = (2 * (τ / η₀ + 1)) * η by ring, mul_pow]
            _ ≤ (2 * (τ / η₀ + 1)) ^ d * (η ^ (d - k) * (1 + η) ^ k) := by gcongr
            _ ≤ max (CT * (C + 1) ^ d) ((2 * (τ / η₀ + 1)) ^ d) * (η ^ (d - k) * (1 + η) ^ k) := by
                gcongr; exact le_max_right _ _
            _ = _ := by ring

/-- `S_L ∩ {⟨𝟙,x⟩ ≤ L(1/t* + η)} = L • P_η`. -/
private theorem logCone_inter_eq (Γ : Finset (Fin d → ℝ)) {L : ℝ} (hL : 0 < L) (η : ℝ) :
    logCone Γ L ∩ {x | ones ⬝ᵥ x ≤ L * ((newtonDist Γ)⁻¹ + η)} = L • dualSlab Γ η := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ hL.ne']
  simp only [logCone, dualSlab, dualPoly, mem_inter_iff, mem_ofPred_eq, Pi.smul_apply,
    smul_eq_mul, dotProduct_smul]
  have hL' : 0 < L⁻¹ := inv_pos.mpr hL
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩
    refine ⟨⟨fun i => mul_nonneg hL'.le (h0 i), fun α hα => ?_⟩, ?_⟩
    · rw [le_inv_mul_iff₀ hL, mul_one]; exact h1 α hα
    · rw [inv_mul_le_iff₀ hL]; exact h2
  · rintro ⟨⟨h0, h1⟩, h2⟩
    refine ⟨⟨fun i => ?_, fun α hα => ?_⟩, ?_⟩
    · have := h0 i; rwa [mul_nonneg_iff_of_pos_left hL'] at this
    · have := h1 α hα; rwa [le_inv_mul_iff₀ hL, mul_one] at this
    · rwa [inv_mul_le_iff₀ hL] at h2

private theorem one_dot_ge_of_logCone {Γ : Finset (Fin d → ℝ)} (hd : 0 < newtonDist Γ) {L : ℝ}
    (hL : 0 < L) {x : Fin d → ℝ} (hx : x ∈ logCone Γ L) : L * (newtonDist Γ)⁻¹ ≤ ones ⬝ᵥ x := by
  have hmem : x ∈ logCone Γ L ∩ {x | ones ⬝ᵥ x ≤ L * ((newtonDist Γ)⁻¹ + (ones ⬝ᵥ x / L))} := by
    refine ⟨hx, ?_⟩
    change ones ⬝ᵥ x ≤ L * ((newtonDist Γ)⁻¹ + ones ⬝ᵥ x / L)
    rw [mul_add, mul_div_cancel₀ _ hL.ne']
    have : 0 ≤ L * (newtonDist Γ)⁻¹ := by positivity
    linarith
  have hmem' : x ∈ L • dualSlab Γ (ones ⬝ᵥ x / L) := by
    rw [← logCone_inter_eq Γ hL]; exact hmem
  rw [mem_smul_set_iff_inv_smul_mem₀ hL.ne'] at hmem'
  have := one_dot_ge hd hmem'.1
  rw [dotProduct_smul, smul_eq_mul, le_inv_mul_iff₀ hL] at this
  exact this

private theorem volume_smul_dualSlab (Γ : Finset (Fin d → ℝ)) {L : ℝ} (hL : 0 < L) (η : ℝ) :
    volume (L • dualSlab Γ η) = ENNReal.ofReal (L ^ d) * volume (dualSlab Γ η) := by
  rw [Measure.addHaar_smul, Module.finrank_fin_fun, abs_of_pos (pow_pos hL d)]

private theorem summable_shell (d : ℕ) :
    Summable fun j : ℕ => ((j : ℝ) + 2) ^ d * Real.exp (-(j : ℝ)) := by
  have h0 := (summable_nat_add_iff 2).mpr (Real.summable_pow_mul_exp_neg_nat_mul d one_pos)
  refine (h0.mul_left (Real.exp 2)).congr fun j => ?_
  simp only [Nat.cast_add, Nat.cast_ofNat, neg_mul, one_mul]
  rw [show -((j : ℝ) + 2) = -(j : ℝ) + -2 by ring, Real.exp_add]
  have : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp 2 * (((j : ℝ) + 2) ^ d * (Real.exp (-(j : ℝ)) * Real.exp (-2)))
      = ((j : ℝ) + 2) ^ d * Real.exp (-(j : ℝ)) * (Real.exp 2 * Real.exp (-2)) := by ring
    _ = _ := by rw [this, mul_one]

/-- (N2 proof) **Upper bound**: `H(L) ≤ C e^{-L/t*} L^{dim O}` for `L ≥ 1`. -/
theorem Hfun_le {Γ : Finset (Fin d → ℝ)} (hd : 0 < newtonDist Γ) :
    ∃ C₄ : ℝ, 0 ≤ C₄ ∧ ∀ L : ℝ, 1 ≤ L →
      Hfun Γ L ≤ ENNReal.ofReal (C₄ * Real.exp (-(L * (newtonDist Γ)⁻¹)) * L ^ optDim Γ) := by
  obtain ⟨C₃, hC₃, hQ⟩ := volume_dualSlab_le hd
  have hk := optDim_le Γ
  set k := optDim Γ
  set τ := (newtonDist Γ)⁻¹
  set S := ∑' j : ℕ, ((j : ℝ) + 2) ^ d * Real.exp (-(j : ℝ))
  have hS : 0 ≤ S := tsum_nonneg fun j => by positivity
  refine ⟨C₃ * S, mul_nonneg hC₃ hS, fun L hL => ?_⟩
  have hL0 : 0 < L := by linarith
  set Sh : ℕ → Set (Fin d → ℝ) := fun j =>
    (logCone Γ L ∩ {x | ones ⬝ᵥ x ≤ L * (τ + ((j : ℝ) + 1) / L)}) ∩
      {x | L * τ + j ≤ ones ⬝ᵥ x}
  have hcover : logCone Γ L ⊆ ⋃ j, Sh j := by
    intro x hx
    have hge := one_dot_ge_of_logCone hd hL0 hx
    set j := ⌊ones ⬝ᵥ x - L * τ⌋₊
    refine mem_iUnion.mpr ⟨j, ⟨hx, ?_⟩, ?_⟩
    · change ones ⬝ᵥ x ≤ L * (τ + ((j : ℝ) + 1) / L)
      rw [mul_add, mul_div_cancel₀ _ hL0.ne']
      have := Nat.lt_floor_add_one (ones ⬝ᵥ x - L * τ)
      linarith
    · change L * τ + j ≤ ones ⬝ᵥ x
      have := Nat.floor_le (sub_nonneg.mpr hge)
      linarith
  have hterm : ∀ j : ℕ, ∫⁻ x in Sh j, ENNReal.ofReal (Real.exp (-(ones ⬝ᵥ x))) ≤
      ENNReal.ofReal (C₃ * Real.exp (-(L * τ)) * L ^ k *
        (((j : ℝ) + 2) ^ d * Real.exp (-(j : ℝ)))) := by
    intro j
    have hη : 0 < ((j : ℝ) + 1) / L := by positivity
    calc ∫⁻ x in Sh j, ENNReal.ofReal (Real.exp (-(ones ⬝ᵥ x)))
        ≤ ∫⁻ _x in Sh j, ENNReal.ofReal (Real.exp (-(L * τ + j))) := by
          refine setLIntegral_mono measurable_const fun x hx => ?_
          have hx2 : L * τ + j ≤ ones ⬝ᵥ x := hx.2
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
      _ = ENNReal.ofReal (Real.exp (-(L * τ + j))) * volume (Sh j) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (Real.exp (-(L * τ + j))) *
            (ENNReal.ofReal (L ^ d) * ENNReal.ofReal (C₃ * (((j : ℝ) + 1) / L) ^ (d - k) *
              (1 + ((j : ℝ) + 1) / L) ^ k)) := by
          gcongr
          calc volume (Sh j) ≤ volume (L • dualSlab Γ (((j : ℝ) + 1) / L)) := by
                rw [← logCone_inter_eq Γ hL0]; exact measure_mono inter_subset_left
            _ = _ := by rw [volume_smul_dualSlab Γ hL0]
            _ ≤ _ := by gcongr; exact hQ _ hη
      _ = ENNReal.ofReal (Real.exp (-(L * τ + j)) * (L ^ d * (C₃ * (((j : ℝ) + 1) / L) ^ (d - k) *
              (1 + ((j : ℝ) + 1) / L) ^ k))) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hLd : L ^ d * (((j : ℝ) + 1) / L) ^ (d - k) = L ^ k * ((j : ℝ) + 1) ^ (d - k) := by
            rw [div_pow, show L ^ d = L ^ k * L ^ (d - k) by rw [← pow_add, Nat.add_sub_cancel' hk]]
            field_simp
          have h1 : 1 + ((j : ℝ) + 1) / L ≤ (j : ℝ) + 2 := by
            have : ((j : ℝ) + 1) / L ≤ (j : ℝ) + 1 := div_le_self (by positivity) hL
            linarith
          have h2 : ((j : ℝ) + 1) ^ (d - k) * ((j : ℝ) + 2) ^ k ≤ ((j : ℝ) + 2) ^ d := by
            calc ((j : ℝ) + 1) ^ (d - k) * ((j : ℝ) + 2) ^ k
                ≤ ((j : ℝ) + 2) ^ (d - k) * ((j : ℝ) + 2) ^ k := by gcongr; linarith
              _ = _ := by rw [← pow_add, Nat.sub_add_cancel hk]
          have hexp : Real.exp (-(L * τ + j)) = Real.exp (-(L * τ)) * Real.exp (-(j : ℝ)) := by
            rw [← Real.exp_add]; ring_nf
          have hA : 0 ≤ (1 + ((j : ℝ) + 1) / L) ^ k := by positivity
          calc Real.exp (-(L * τ + j)) * (L ^ d * (C₃ * (((j : ℝ) + 1) / L) ^ (d - k) *
                (1 + ((j : ℝ) + 1) / L) ^ k))
              = C₃ * Real.exp (-(L * τ)) * Real.exp (-(j : ℝ)) *
                  ((L ^ d * (((j : ℝ) + 1) / L) ^ (d - k)) * (1 + ((j : ℝ) + 1) / L) ^ k) := by
                rw [hexp]; ring
            _ = C₃ * Real.exp (-(L * τ)) * Real.exp (-(j : ℝ)) * L ^ k *
                  (((j : ℝ) + 1) ^ (d - k) * (1 + ((j : ℝ) + 1) / L) ^ k) := by rw [hLd]; ring
            _ ≤ C₃ * Real.exp (-(L * τ)) * Real.exp (-(j : ℝ)) * L ^ k *
                  (((j : ℝ) + 1) ^ (d - k) * ((j : ℝ) + 2) ^ k) := by gcongr
            _ ≤ C₃ * Real.exp (-(L * τ)) * Real.exp (-(j : ℝ)) * L ^ k * ((j : ℝ) + 2) ^ d := by
                gcongr
            _ = _ := by ring
  calc Hfun Γ L ≤ ∫⁻ x in ⋃ j, Sh j, ENNReal.ofReal (Real.exp (-(ones ⬝ᵥ x))) :=
        lintegral_mono_set hcover
    _ ≤ ∑' j, ∫⁻ x in Sh j, ENNReal.ofReal (Real.exp (-(ones ⬝ᵥ x))) := lintegral_iUnion_le _ _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (C₃ * Real.exp (-(L * τ)) * L ^ k *
          (((j : ℝ) + 2) ^ d * Real.exp (-(j : ℝ)))) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (C₃ * Real.exp (-(L * τ)) * L ^ k * S) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
          ((summable_shell d).mul_left _), tsum_mul_left]
    _ = _ := by congr 1; ring

end SLT.Newton
