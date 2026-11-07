/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Tubes around sets of affine dimension `k` (N2, volume step)

`volume_thicken_le`: if `A ⊆ ℝ^d` is compact and its affine span has dimension `k`, then
`vol(A + closedBall 0 r) ≤ C r^{d-k}` for `0 < r ≤ 1` (sup norm).

Proof:
* pick a minimal set `I` of coordinates that is injective on `W = direction (affineSpan A)`;
  minimality gives `|I|` linearly independent vectors of `W`, so `|I| ≤ k`;
* the restriction to `I` is antilipschitz on `W`, so points of the tube with the same
  `I`-coordinates are `O(r)` apart;
* Fubini over the split `ℝ^I × ℝ^{Iᶜ}`: every slice lies in a ball of radius `O(r)` in
  `ℝ^{Iᶜ}`, and `|Iᶜ| ≥ d - k`.
-/

@[expose] public section

namespace SLT.Newton

open MeasureTheory Set Metric Module
open scoped Pointwise

variable {d : ℕ}

/-- A set of at most `finrank W` coordinates that is injective on `W`. -/
theorem exists_coords_injOn (W : Submodule ℝ (Fin d → ℝ)) :
    ∃ I : Finset (Fin d), I.card ≤ finrank ℝ W ∧
      ∀ w ∈ W, (∀ i ∈ I, w i = 0) → w = 0 := by
  classical
  set P : Finset (Fin d) → Prop := fun I => ∀ w ∈ W, (∀ i ∈ I, w i = 0) → w = 0
  have hU : P Finset.univ := fun w _ hw => funext fun i => hw i (Finset.mem_univ i)
  obtain ⟨I, hI, hmin⟩ := (Finset.univ.powerset.filter P).exists_min_image Finset.card
    ⟨Finset.univ, by simp [hU]⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hI hmin
  refine ⟨I, ?_, hI.2⟩
  -- minimality: for each `i ∈ I` a witness `w_i ∈ W` vanishing on `I \ {i}` with `w_i i ≠ 0`
  have hwit : ∀ i ∈ I, ∃ w ∈ W, (∀ j ∈ I, j ≠ i → w j = 0) ∧ w i ≠ 0 := by
    intro i hi
    by_contra h
    push Not at h
    have hP : P (I.erase i) := fun w hw hw0 => hI.2 w hw fun j hj => by
      by_cases hji : j = i
      · subst hji
        exact h w hw fun k hk hki => hw0 k (Finset.mem_erase.mpr ⟨hki, hk⟩)
      · exact hw0 j (Finset.mem_erase.mpr ⟨hji, hj⟩)
    have := hmin (I.erase i) ⟨(Finset.erase_subset _ _).trans hI.1, hP⟩
    rw [Finset.card_erase_of_mem hi] at this
    have : 0 < I.card := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  choose w hwW hw0 hwne using hwit
  set v : I → W := fun i => ⟨w i.1 i.2, hwW i.1 i.2⟩
  have hli : LinearIndependent ℝ v := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have hcoord := congrArg (fun x : W => (x : Fin d → ℝ) i.1) hg
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Submodule.coe_zero, Pi.zero_apply, v] at hcoord
    rw [Finset.sum_eq_single i (fun j _ hji => by
      rw [hw0 j.1 j.2 i.1 i.2 (fun h => hji (Subtype.ext h).symm), mul_zero])
      (fun h => absurd hi h)] at hcoord
    exact (mul_eq_zero.mp hcoord).resolve_right (hwne i.1 i.2)
  have := hli.fintype_card_le_finrank
  simpa using this

/-- **Tube volume**: a compact set of affine dimension `k`, thickened by `r ≤ 1`, has volume
`≤ C r^{d-k}`. -/
theorem volume_thicken_le {A : Set (Fin d → ℝ)} (hA : IsCompact A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      volume (A + closedBall (0 : Fin d → ℝ) r) ≤
        ENNReal.ofReal (C * r ^ (d - finrank ℝ (affineSpan ℝ A).direction)) := by
  classical
  set W := (affineSpan ℝ A).direction
  set k := finrank ℝ W
  obtain ⟨I, hIk, hI⟩ := exists_coords_injOn W
  -- the restriction to `I`, as a linear map on `W`
  set πI : W →ₗ[ℝ] ({i // i ∈ I} → ℝ) :=
    { toFun := fun w i => (w : Fin d → ℝ) i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker πI = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have := hI w w.2 fun i hi => congrFun hw ⟨i, hi⟩
    exact Subtype.ext this
  obtain ⟨K, hK, hKanti⟩ := πI.exists_antilipschitzWith hker
  obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).mp hA.isBounded
  set D : ℝ := 2 * K + 2
  have hD : 0 ≤ D := by positivity
  refine ⟨(2 * (|R| + 1)) ^ I.card * (2 * D) ^ (d - I.card), by positivity, fun r hr hr1 => ?_⟩
  set T := A + closedBall (0 : Fin d → ℝ) r
  have hTc : IsClosed T := isClosed_closedBall.add_left_of_isCompact hA
  -- points of `T` with the same `I`-coordinates are `D r` apart
  have hdiam : ∀ x ∈ T, ∀ x' ∈ T, (∀ i ∈ I, x i = x' i) → ‖x - x'‖ ≤ D * r := by
    rintro _ ⟨a, ha, y, hy, rfl⟩ _ ⟨a', ha', y', hy', rfl⟩ hxx
    rw [mem_closedBall, dist_zero_right] at hy hy'
    have hW : a - a' ∈ W := by
      show a - a' ∈ (affineSpan ℝ A).direction
      rw [direction_affineSpan]; exact vsub_mem_vectorSpan ℝ ha ha'
    have hπ : ‖πI ⟨a - a', hW⟩‖ ≤ 2 * r := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
      have h := hxx i.1 i.2
      simp only [Pi.add_apply] at h
      have : (a - a') i.1 = y' i.1 - y i.1 := by simp only [Pi.sub_apply]; linarith
      show ‖(a - a') i.1‖ ≤ 2 * r
      rw [this]
      calc ‖y' i.1 - y i.1‖ ≤ ‖y' i.1‖ + ‖y i.1‖ := norm_sub_le _ _
        _ ≤ ‖y'‖ + ‖y‖ := add_le_add (norm_le_pi_norm y' _) (norm_le_pi_norm y _)
        _ ≤ 2 * r := by linarith
    have haa : ‖a - a'‖ ≤ K * (2 * r) := by
      have := hKanti.le_mul_dist ⟨a - a', hW⟩ 0
      simp only [dist_zero_right, map_zero] at this
      calc ‖a - a'‖ = ‖(⟨a - a', hW⟩ : W)‖ := rfl
        _ ≤ K * ‖πI ⟨a - a', hW⟩‖ := this
        _ ≤ K * (2 * r) := mul_le_mul_of_nonneg_left hπ (NNReal.coe_nonneg K)
    calc ‖a + y - (a' + y')‖ = ‖(a - a') + (y - y')‖ := by congr 1; abel
      _ ≤ ‖a - a'‖ + ‖y - y'‖ := norm_add_le _ _
      _ ≤ K * (2 * r) + (‖y‖ + ‖y'‖) := add_le_add haa (norm_sub_le _ _)
      _ ≤ D * r := by simp only [D]; nlinarith
  have hTbdd : ∀ x ∈ T, ‖x‖ ≤ |R| + 1 := by
    rintro _ ⟨a, ha, y, hy, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hy
    calc ‖a + y‖ ≤ ‖a‖ + ‖y‖ := norm_add_le _ _
      _ ≤ |R| + 1 := add_le_add ((hR a ha).trans (le_abs_self R)) (hy.trans hr1)
  -- Fubini over the coordinate split
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (· ∈ I)
  have hmp := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (· ∈ I)
  have hS : MeasurableSet (e.symm ⁻¹' T) := e.symm.measurable hTc.measurableSet
  have hvol : volume T = volume (e.symm ⁻¹' T) := by
    convert (hmp.symm.measure_preimage (s := T) hTc.measurableSet.nullMeasurableSet).symm
      using 7
  rw [hvol, Measure.volume_eq_prod, Measure.prod_apply hS]
  set c := Fintype.card {i // i ∉ I}
  have hc : c = d - I.card := by simp [c, Fintype.card_subtype_compl]
  -- each slice is in a small ball, and empty unless `y` is in a bounded ball
  have hslice : ∀ y : {i // i ∈ I} → ℝ, volume (Prod.mk y ⁻¹' (e.symm ⁻¹' T)) ≤
      (closedBall (0 : {i // i ∈ I} → ℝ) (|R| + 1)).indicator
        (fun _ => ENNReal.ofReal ((2 * (D * r)) ^ c)) y := by
    intro y
    by_cases hne : (Prod.mk y ⁻¹' (e.symm ⁻¹' T)).Nonempty
    · obtain ⟨z₀, hz₀⟩ := hne
      have hy : y ∈ closedBall (0 : {i // i ∈ I} → ℝ) (|R| + 1) := by
        rw [mem_closedBall, dist_zero_right]
        refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
        have := norm_le_pi_norm (e.symm (y, z₀)) i.1
        simp only [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply,
          MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk, i.2, dite_true] at this
        exact this.trans (hTbdd _ hz₀)
      rw [indicator_of_mem hy]
      refine (measure_mono fun z hz => ?_).trans
        (Real.volume_pi_closedBall z₀ (by positivity)).le
      rw [mem_closedBall, dist_eq_norm]
      have h := hdiam _ hz _ hz₀ fun i hi => by
        simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
      have := norm_le_pi_norm (e.symm (y, z) - e.symm (y, z₀)) i.1
      simp only [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply,
        MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk, Pi.sub_apply, i.2, dite_false] at this
      exact this.trans h
    · rw [not_nonempty_iff_eq_empty] at hne
      rw [hne, measure_empty]; exact zero_le
  calc ∫⁻ y, volume (Prod.mk y ⁻¹' (e.symm ⁻¹' T))
      ≤ ∫⁻ y, (closedBall (0 : {i // i ∈ I} → ℝ) (|R| + 1)).indicator
          (fun _ => ENNReal.ofReal ((2 * (D * r)) ^ c)) y := lintegral_mono hslice
    _ = ENNReal.ofReal ((2 * (D * r)) ^ c) * volume (closedBall (0 : {i // i ∈ I} → ℝ) (|R| + 1)) := by
        rw [lintegral_indicator_const measurableSet_closedBall, mul_comm]
    _ = ENNReal.ofReal ((2 * (D * r)) ^ c * (2 * (|R| + 1)) ^ I.card) := by
        rw [Real.volume_pi_closedBall _ (by positivity), Fintype.card_coe,
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [hc]
        have hpow : r ^ (d - I.card) ≤ r ^ (d - k) :=
          pow_le_pow_of_le_one hr.le hr1 (by omega)
        have e1 : (2 * (D * r)) ^ (d - I.card) = (2 * D) ^ (d - I.card) * r ^ (d - I.card) := by
          rw [← mul_pow]; ring
        rw [e1]
        have h1 : 0 ≤ (2 * D) ^ (d - I.card) := by positivity
        have h2 : 0 ≤ (2 * (|R| + 1)) ^ I.card := by positivity
        calc (2 * D) ^ (d - I.card) * r ^ (d - I.card) * (2 * (|R| + 1)) ^ I.card
            ≤ (2 * D) ^ (d - I.card) * r ^ (d - k) * (2 * (|R| + 1)) ^ I.card := by gcongr
          _ = (2 * (|R| + 1)) ^ I.card * (2 * D) ^ (d - I.card) * r ^ (d - k) := by ring

end SLT.Newton
