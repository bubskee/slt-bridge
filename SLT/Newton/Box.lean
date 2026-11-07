/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Newton.TwoSided
public import SLT.NormalCrossing.Box

/-!
# N2 on a symmetric box, with units

`newton_box_units`: if `c Σ|w|^α ≤ K ≤ C Σ|w|^α` on `[-δ,δ]^d` and the prior density `f` lies
between two positive constants there, then
`Z(N) = ∫_{[-δ,δ]^d} e^{-N K} f` has learning pair `(1/t*, newtonMult Γ)`.

Proof, as in M2's `normalCrossing_box_units`: the box is covered by the `2^d` reflected orthants
`refl ε ⁻¹' [0,δ]^d`. Each piece is `δ^d` times a unit-box integral of
`K_ε(x) = K(refl ε (δ x))`, and `K_ε` is again comparable to `Σ|x|^α`: reflections keep `|w_i|`,
and scaling multiplies `|w|^α` by `δ^{Σα_i}`. N2 (`newtonTwoSided`) gives each piece the pair. The
lower bound comes from one piece and the upper bound from the sum over all pieces. Densities
between constants do not change the pair (`HasLaplacePair.withDensity`).

N3's reduced-rank-regression instance (loss `Σ b_i² a_j²` on a symmetric neighbourhood) has
exactly this shape.
-/

@[expose] public section

namespace SLT.Newton

open MeasureTheory Set Filter Module
open scoped ENNReal

variable {d : ℕ}

private theorem refl_refl (ε : Fin d → Bool) (y : Fin d → ℝ) : refl ε (refl ε y) = y := by
  funext i; unfold refl; split_ifs <;> simp

private theorem monomial_refl_smul {δ : ℝ} (hδ : 0 < δ) (ε : Fin d → Bool) (α x : Fin d → ℝ) :
    monomial α (refl ε (δ • x)) = δ ^ (∑ i, α i) * monomial α x := by
  have habs : ∀ i, |refl ε (δ • x) i| = δ * |x i| := fun i => by
    unfold refl; split_ifs <;> simp [abs_mul, abs_of_pos hδ]
  simp only [monomial, habs, Real.mul_rpow hδ.le (abs_nonneg _), Finset.prod_mul_distrib,
    Real.rpow_sum_of_pos hδ]

/-- Scaling `[0,δ]^d → [0,1]^d`. -/
private theorem lintegral_posBox_scale {δ : ℝ} (hδ : 0 < δ) {g : (Fin d → ℝ) → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ y in posBox δ, g y = ENNReal.ofReal (δ ^ d) * ∫⁻ x in Icc (0 : Fin d → ℝ) 1, g (δ • x) := by
  set L : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) := δ • LinearMap.id
  have hdet : LinearMap.det L = δ ^ d := by
    simp [L, LinearMap.det_smul, Module.finrank_fintype_fun_eq_card]
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := L) (by rw [hdet]; positivity)
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  have hP : MeasurableSet (posBox (d := d) δ) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have key : ∫⁻ x, (posBox δ).indicator g (L x) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| * ∫⁻ y, (posBox δ).indicator g y := by
    rw [← lintegral_map (hg.indicator hP) hLm, hmap, lintegral_smul_measure, smul_eq_mul]
  rw [hdet, abs_of_pos (by positivity), lintegral_indicator hP] at key
  have hpt : ∀ x : Fin d → ℝ, (posBox δ).indicator g (L x) =
      (Icc (0 : Fin d → ℝ) 1).indicator (fun x => g (δ • x)) x := by
    intro x
    have hmem : L x ∈ posBox δ ↔ x ∈ Icc (0 : Fin d → ℝ) 1 := by
      simp only [posBox, Set.mem_pi, mem_univ, forall_const, mem_Icc, L, LinearMap.smul_apply,
        LinearMap.id_apply, Pi.smul_apply, smul_eq_mul, Pi.le_def, Pi.zero_apply, Pi.one_apply]
      constructor
      · intro h
        exact ⟨fun i => nonneg_of_mul_nonneg_right (by linarith [(h i).1]) hδ,
          fun i => by nlinarith [(h i).2]⟩
      · rintro ⟨h1, h2⟩ i
        exact ⟨mul_nonneg hδ.le (h1 i), by nlinarith [h2 i]⟩
    by_cases hx : x ∈ Icc (0 : Fin d → ℝ) 1
    · rw [indicator_of_mem (hmem.mpr hx), indicator_of_mem hx]; rfl
    · rw [indicator_of_notMem (fun h' => hx (hmem.mp h')), indicator_of_notMem hx]
  simp_rw [hpt] at key
  rw [lintegral_indicator measurableSet_Icc] at key
  have hδd : ENNReal.ofReal (δ ^ d) * ENNReal.ofReal (δ ^ d)⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]
  rw [key, ← mul_assoc, hδd, one_mul]

/-- **N2 on the symmetric box `[-δ,δ]^d`, with units.** -/
theorem newton_box_units {δ : ℝ} (hδ : 0 < δ) {Γ : Finset (Fin d → ℝ)}
    (hΓ : ∀ α ∈ Γ, ∀ i, 0 ≤ α i) (hd : 0 < newtonDist Γ) {K : (Fin d → ℝ) → ℝ}
    (hK : Measurable K) {f : (Fin d → ℝ) → ℝ≥0∞} {a b c C : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hKlo : ∀ y ∈ box δ, c * monoSum Γ y ≤ K y) (hKhi : ∀ y ∈ box δ, K y ≤ C * monoSum Γ y)
    (hflo : ∀ y ∈ box δ, ENNReal.ofReal a ≤ f y) (hfhi : ∀ y ∈ box δ, f y ≤ ENNReal.ofReal b) :
    HasLaplacePair (Z ((volume.restrict (box δ)).withDensity f) K) (newtonDist Γ)⁻¹
      (newtonMult Γ) := by
  have hB := measurableSet_box (d := d) δ
  have hne := nonempty_of_newtonDist_pos hd
  set τ := (newtonDist Γ)⁻¹
  set m := newtonMult Γ
  -- scaling constants
  set cmin := Γ.inf' hne fun α => δ ^ (∑ i, α i)
  set cmax := Γ.sup' hne fun α => δ ^ (∑ i, α i)
  have hcmin : 0 < cmin := (Finset.lt_inf'_iff hne).mpr fun α _ => Real.rpow_pos_of_pos hδ _
  have hscale : ∀ ε x, monoSum Γ (refl ε (δ • x)) = ∑ α ∈ Γ, δ ^ (∑ i, α i) * monomial α x :=
    fun ε x => Finset.sum_congr rfl fun α _ => monomial_refl_smul hδ ε α x
  have hlo' : ∀ ε x, cmin * monoSum Γ x ≤ monoSum Γ (refl ε (δ • x)) := fun ε x => by
    rw [hscale, monoSum, Finset.mul_sum]
    exact Finset.sum_le_sum fun α hα =>
      mul_le_mul_of_nonneg_right (Finset.inf'_le _ hα) (monomial_nonneg α x)
  have hhi' : ∀ ε x, monoSum Γ (refl ε (δ • x)) ≤ cmax * monoSum Γ x := fun ε x => by
    rw [hscale, monoSum, Finset.mul_sum]
    exact Finset.sum_le_sum fun α hα =>
      mul_le_mul_of_nonneg_right (Finset.le_sup' (fun α => δ ^ (∑ i, α i)) hα) (monomial_nonneg α x)
  have hmemB : ∀ ε, ∀ x ∈ Icc (0 : Fin d → ℝ) 1, refl ε (δ • x) ∈ box δ := fun ε x hx i _ => by
    have h0 := hx.1 i; have h1 := hx.2 i
    simp only [Pi.zero_apply, Pi.one_apply] at h0 h1
    unfold refl
    split_ifs <;> simp only [Pi.smul_apply, smul_eq_mul, mem_Icc] <;> constructor <;> nlinarith
  -- each reflected, rescaled piece has the pair, by N2
  set Kε : (Fin d → Bool) → (Fin d → ℝ) → ℝ := fun ε x => K (refl ε (δ • x))
  have hpiece : ∀ ε, HasLaplacePair (Z (volume.restrict (Icc (0 : Fin d → ℝ) 1)) (Kε ε)) τ m := by
    intro ε
    have hrm : Measurable (refl ε : (Fin d → ℝ) → (Fin d → ℝ)) :=
      (measurePreserving_refl ε).measurable
    refine newtonTwoSided d Γ hΓ hd (Kε ε) (hK.comp (hrm.comp (measurable_const_smul δ)))
      (c * cmin) (max C 0 * cmax) (mul_pos hc hcmin) fun x hx => ⟨?_, ?_⟩
    · have := hKlo _ (hmemB ε x hx)
      calc c * cmin * ∑ α ∈ Γ, monomial α x = c * (cmin * monoSum Γ x) := by rw [monoSum]; ring
        _ ≤ c * monoSum Γ (refl ε (δ • x)) := mul_le_mul_of_nonneg_left (hlo' ε x) hc.le
        _ ≤ Kε ε x := this
    · have := hKhi _ (hmemB ε x hx)
      have hM0 := monoSum_nonneg Γ (refl ε (δ • x))
      calc Kε ε x ≤ C * monoSum Γ (refl ε (δ • x)) := this
        _ ≤ max C 0 * monoSum Γ (refl ε (δ • x)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hM0
        _ ≤ max C 0 * (cmax * monoSum Γ x) :=
            mul_le_mul_of_nonneg_left (hhi' ε x) (le_max_right _ _)
        _ = max C 0 * cmax * ∑ α ∈ Γ, monomial α x := by rw [monoSum]; ring
  -- the piece integrals
  set G : ℝ → (Fin d → ℝ) → ℝ≥0∞ := fun N y => ENNReal.ofReal (Real.exp (-(N * K y)))
  have hGm : ∀ N, Measurable (G N) := fun N => by
    change Measurable fun y => ENNReal.ofReal (Real.exp (-(N * K y)))
    fun_prop
  have hP : MeasurableSet (posBox (d := d) δ) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hpiece_eq : ∀ ε N, ∫⁻ y in refl ε ⁻¹' posBox δ, G N y =
      ENNReal.ofReal (δ ^ d) * Z (volume.restrict (Icc (0 : Fin d → ℝ) 1)) (Kε ε) N := by
    intro ε N
    have hrm : Measurable (refl ε : (Fin d → ℝ) → (Fin d → ℝ)) :=
      (measurePreserving_refl ε).measurable
    have h1 := (measurePreserving_refl ε).setLIntegral_comp_preimage hP ((hGm N).comp hrm)
    simp only [Function.comp_apply, refl_refl] at h1
    rw [h1, lintegral_posBox_scale hδ (g := fun y => G N (refl ε y)) ((hGm N).comp hrm)]
    rfl
  have hZ : ∀ N, Z (volume.restrict (box δ)) K N = ∫⁻ y in box δ, G N y := fun N => rfl
  have hupper : ∀ N, Z (volume.restrict (box δ)) K N ≤
      ∑ ε : Fin d → Bool, ENNReal.ofReal (δ ^ d) *
        Z (volume.restrict (Icc (0 : Fin d → ℝ) 1)) (Kε ε) N := by
    intro N
    rw [hZ]
    calc ∫⁻ y in box δ, G N y ≤ ∫⁻ y in ⋃ ε : Fin d → Bool, refl ε ⁻¹' posBox δ, G N y :=
          lintegral_mono_set (box_subset_iUnion δ)
      _ ≤ ∑' ε : Fin d → Bool, ∫⁻ y in refl ε ⁻¹' posBox δ, G N y := lintegral_iUnion_le _ _
      _ = _ := by rw [tsum_fintype]; exact Finset.sum_congr rfl fun ε _ => hpiece_eq ε N
  set ε₀ : Fin d → Bool := fun _ => true
  have hlower : ∀ N, ENNReal.ofReal (δ ^ d) *
      Z (volume.restrict (Icc (0 : Fin d → ℝ) 1)) (Kε ε₀) N ≤ Z (volume.restrict (box δ)) K N := by
    intro N
    rw [← hpiece_eq, hZ]
    refine lintegral_mono_set fun y hy i _ => ?_
    have := hy i (mem_univ i)
    simp only [refl, ε₀, ite_true, mem_Icc] at this
    exact ⟨by linarith [this.1], this.2⟩
  have hδd : ENNReal.ofReal (δ ^ d) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hpair : HasLaplacePair (Z (volume.restrict (box δ)) K) τ m := by
    refine ⟨(hpiece ε₀).1, ?_, ?_⟩
    · exact ((hpiece ε₀).2.1.const_mul hδd ENNReal.ofReal_ne_top).mono
        (Eventually.of_forall hlower)
    · exact (LaplaceUpper.finset_sum Finset.univ fun ε _ =>
        (hpiece ε).2.2.const_mul ENNReal.ofReal_ne_top).mono (Eventually.of_forall hupper)
  exact hpair.withDensity (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top ((ae_restrict_iff' hB).mpr (Eventually.of_forall hflo))
    ((ae_restrict_iff' hB).mpr (Eventually.of_forall hfhi))

end SLT.Newton
