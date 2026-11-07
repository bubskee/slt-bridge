/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.NormalCrossing.Cube
public import SLT.Laplace.Integral

/-!
# Normal crossing on a symmetric box, with units

This is the chart-local form that resolution of singularities produces. On the box
`[-δ, δ]^d ⊆ ℝ^d` take

* the loss `K(y) = ∏ |yᵢ|^{kᵢ}` (`absLoss`), with `kᵢ ∈ ℕ` and some `kᵢ ≠ 0`;
* the prior `∏ |yᵢ|^{hᵢ} dy` (`absDens`), with `hᵢ > -1`.

Then `Z(N) = ∫_{[-δ,δ]^d} e^{-N K} ∏|yᵢ|^{hᵢ} dy` has the pair `(λ, m) = (ncLam k h, ncMult k h)`
(`normalCrossing_box`). The same holds with units (`normalCrossing_box_units`): a loss between
`c K` and `C K`, and a prior density between `a ∏|yᵢ|^{hᵢ}` and `b ∏|yᵢ|^{hᵢ}` on the box.

Proof: the integrand depends only on `|y|`. Reflections `yᵢ ↦ ±yᵢ` preserve Lebesgue measure,
so `Z_box` lies between `Z₊` and `2^d Z₊`, where `Z₊` is the integral over `(0, δ]^d`
(`Z_box_le`, `Z_pos_le_box`). The scaling `y = δ x` turns `Z₊` into a constant times
`ncZ k h (c N)` (`Z_pos_scale`).
-/

@[expose] public section

namespace SLT

open MeasureTheory Set Filter Real NC
open scoped ENNReal

variable {d : ℕ}

/-- The monomial loss `∏ |yᵢ|^{kᵢ}`. -/
noncomputable def absLoss (k : Fin d → ℕ) (y : Fin d → ℝ) : ℝ := ∏ i, |y i| ^ k i

/-- The monomial density `∏ |yᵢ|^{hᵢ}`. -/
noncomputable def absDens (h : Fin d → ℝ) (y : Fin d → ℝ) : ℝ := ∏ i, |y i| ^ h i

/-- The box `[-δ, δ]^d`. -/
def box (δ : ℝ) : Set (Fin d → ℝ) := Set.pi univ fun _ => Icc (-δ) δ

/-- The box measure `1_{[-δ,δ]^d} ∏ |yᵢ|^{hᵢ} dy`. -/
noncomputable def boxMeasure (δ : ℝ) (h : Fin d → ℝ) : Measure (Fin d → ℝ) :=
  (volume.restrict (box δ)).withDensity fun y => ENNReal.ofReal (absDens h y)

theorem measurableSet_box (δ : ℝ) : MeasurableSet (box (d := d) δ) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

theorem absDens_nonneg (h : Fin d → ℝ) (y : Fin d → ℝ) : 0 ≤ absDens h y :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _

theorem measurable_absLoss (k : Fin d → ℕ) : Measurable (absLoss k) := by
  unfold absLoss; fun_prop

theorem measurable_absDens (h : Fin d → ℝ) : Measurable (absDens h) := by
  unfold absDens; fun_prop

/-- The integrand `e^{-N K(y)} ∏ |yᵢ|^{hᵢ}`. -/
noncomputable def boxIntegrand (k : Fin d → ℕ) (h : Fin d → ℝ) (N : ℝ) (y : Fin d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(N * absLoss k y)) * absDens h y)

theorem measurable_boxIntegrand (k : Fin d → ℕ) (h : Fin d → ℝ) (N : ℝ) :
    Measurable (boxIntegrand k h N) := by
  unfold boxIntegrand
  have := measurable_absLoss k; have := measurable_absDens h; fun_prop

theorem Z_boxMeasure (δ : ℝ) (k : Fin d → ℕ) (h : Fin d → ℝ) (N : ℝ) :
    Z (boxMeasure δ h) (absLoss k) N = ∫⁻ y in box δ, boxIntegrand k h N y := by
  unfold Z boxMeasure boxIntegrand
  rw [lintegral_withDensity_eq_lintegral_mul _ (by have := measurable_absDens h; fun_prop)
    (by have := measurable_absLoss k; fun_prop)]
  congr 1; funext y
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (absDens_nonneg h y), mul_comm]

/-! ### Reflections -/

/-- The reflection `yᵢ ↦ yᵢ` if `εᵢ`, `yᵢ ↦ -yᵢ` otherwise. -/
def refl (ε : Fin d → Bool) (y : Fin d → ℝ) : Fin d → ℝ := fun i => if ε i then y i else -y i

theorem measurePreserving_refl (ε : Fin d → Bool) :
    MeasurePreserving (refl ε) (volume : Measure (Fin d → ℝ)) volume := by
  have := measurePreserving_pi (fun _ : Fin d => (volume : Measure ℝ)) (fun _ => volume)
    (f := fun i (t : ℝ) => if ε i then t else -t) (fun i => by
      by_cases hε : ε i
      · simp only [hε, ite_true]; exact MeasurePreserving.id _
      · simp only [hε]; exact Measure.measurePreserving_neg _)
  exact this

theorem boxIntegrand_refl (k : Fin d → ℕ) (h : Fin d → ℝ) (N : ℝ) (ε : Fin d → Bool)
    (y : Fin d → ℝ) : boxIntegrand k h N (refl ε y) = boxIntegrand k h N y := by
  have e : ∀ i, |refl ε y i| = |y i| := fun i => by
    unfold refl; split_ifs <;> simp
  simp only [boxIntegrand, absLoss, absDens, e]

/-- The closed positive orthant `[0, δ]^d`. -/
def posBox (δ : ℝ) : Set (Fin d → ℝ) := Set.pi univ fun _ => Icc 0 δ

/-- The half-open positive orthant `(0, δ]^d`. -/
def posBox' (δ : ℝ) : Set (Fin d → ℝ) := Set.pi univ fun _ => Ioc 0 δ

theorem box_subset_iUnion (δ : ℝ) :
    box (d := d) δ ⊆ ⋃ ε : Fin d → Bool, refl ε ⁻¹' posBox δ := by
  intro y hy
  refine mem_iUnion.mpr ⟨fun i => decide (0 ≤ y i), fun i _ => ?_⟩
  have hyi : y i ∈ Icc (-δ) δ := hy i (mem_univ i)
  simp only [refl]
  by_cases h0 : 0 ≤ y i
  · simp only [h0, decide_true, ite_true]; exact ⟨h0, hyi.2⟩
  · have h0' : y i < 0 := lt_of_not_ge h0
    simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨by linarith, by linarith [hyi.1]⟩

theorem lintegral_posBox_eq (δ : ℝ) (f : (Fin d → ℝ) → ℝ≥0∞) :
    ∫⁻ y in posBox δ, f y = ∫⁻ y in posBox' δ, f y := by
  have hae : (posBox' δ : Set (Fin d → ℝ)) =ᵐ[(volume : Measure (Fin d → ℝ))] posBox δ :=
    Measure.pi_Ioc_ae_eq_pi_Icc (μ := fun _ => volume) (s := univ)
      (f := fun _ : Fin d => (0 : ℝ)) (g := fun _ => δ)
  rw [Measure.restrict_congr_set hae]

/-- `Z_box ≤ 2^d Z₊` (written with `Fintype.card (Fin d → Bool)`). -/
theorem Z_box_le (δ : ℝ) (k : Fin d → ℕ) (h : Fin d → ℝ) (N : ℝ) :
    ∫⁻ y in box δ, boxIntegrand k h N y ≤
      (Fintype.card (Fin d → Bool) : ℝ≥0∞) * ∫⁻ y in posBox' δ, boxIntegrand k h N y := by
  have hmeas : MeasurableSet (posBox (d := d) δ) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  calc ∫⁻ y in box δ, boxIntegrand k h N y
      ≤ ∫⁻ y in ⋃ ε : Fin d → Bool, refl ε ⁻¹' posBox δ, boxIntegrand k h N y :=
        lintegral_mono_set (box_subset_iUnion δ)
    _ ≤ ∑' ε : Fin d → Bool, ∫⁻ y in refl ε ⁻¹' posBox δ, boxIntegrand k h N y :=
        lintegral_iUnion_le _ _
    _ = ∑ ε : Fin d → Bool, ∫⁻ y in posBox' δ, boxIntegrand k h N y := by
        rw [tsum_fintype]
        refine Finset.sum_congr rfl fun ε _ => ?_
        rw [← lintegral_posBox_eq, show (∫⁻ y in refl ε ⁻¹' posBox δ, boxIntegrand k h N y) =
          ∫⁻ y in refl ε ⁻¹' posBox δ, boxIntegrand k h N (refl ε y) from
            lintegral_congr fun y => (boxIntegrand_refl k h N ε y).symm]
        exact (measurePreserving_refl ε).setLIntegral_comp_preimage hmeas
          (measurable_boxIntegrand k h N)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem Z_pos_le_box {δ : ℝ} (k : Fin d → ℕ) (h : Fin d → ℝ) (N : ℝ) :
    ∫⁻ y in posBox' δ, boxIntegrand k h N y ≤ ∫⁻ y in box δ, boxIntegrand k h N y :=
  lintegral_mono_set (Set.pi_mono fun _ _ x hx => ⟨by linarith [hx.1, hx.2], hx.2⟩)

/-! ### Scaling `(0, δ]^d → (0, 1]^d` -/

theorem Z_pos_scale {δ : ℝ} (hδ : 0 < δ) (k : Fin d → ℕ) (h : Fin d → ℝ) (N : ℝ) :
    ENNReal.ofReal (δ ^ d)⁻¹ * ∫⁻ y in posBox' δ, boxIntegrand k h N y =
      ENNReal.ofReal (∏ i, δ ^ h i) * ncZ k h ((∏ i, δ ^ k i) * N) := by
  set L : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) := δ • LinearMap.id
  have hdet : LinearMap.det L = δ ^ d := by
    simp [L, LinearMap.det_smul, Module.finrank_fintype_fun_eq_card]
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := L)
    (by rw [hdet]; positivity)
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  have hP : MeasurableSet (posBox' (d := d) δ) := MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  have hC : MeasurableSet (Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) 1) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  have hg : Measurable ((posBox' δ).indicator (boxIntegrand k h N)) :=
    (measurable_boxIntegrand k h N).indicator hP
  have key : ∫⁻ x, (posBox' δ).indicator (boxIntegrand k h N) (L x) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| * ∫⁻ y, (posBox' δ).indicator (boxIntegrand k h N) y := by
    rw [← lintegral_map hg hLm, hmap, lintegral_smul_measure, smul_eq_mul]
  rw [hdet, abs_of_pos (by positivity), lintegral_indicator hP] at key
  rw [← key]
  have hpt : ∀ x : Fin d → ℝ, (posBox' δ).indicator (boxIntegrand k h N) (L x) =
      (Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal
        (∏ i, δ ^ h i) * ENNReal.ofReal (Real.exp (-((∏ i, δ ^ k i) * N * ∏ i, x i ^ k i)) *
          ∏ i, x i ^ h i)) x := by
    intro x
    have hLx : ∀ i, L x i = δ * x i := fun i => rfl
    have hmem : L x ∈ posBox' δ ↔ x ∈ Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) 1 := by
      simp only [posBox', Set.mem_pi, mem_univ, forall_const, mem_Ioc, hLx]
      refine forall_congr' fun i => ?_
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨pos_of_mul_pos_right h1 hδ.le, by nlinarith⟩
      · rintro ⟨h1, h2⟩
        exact ⟨mul_pos hδ h1, by nlinarith⟩
    by_cases hx : x ∈ Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) 1
    · rw [indicator_of_mem (hmem.mpr hx), indicator_of_mem hx]
      have hxi : ∀ i, 0 < x i := fun i => (hx i (mem_univ i)).1
      have habs : ∀ i, |L x i| = δ * x i := fun i => by
        rw [hLx]; exact abs_of_pos (mul_pos hδ (hxi i))
      simp only [boxIntegrand, absLoss, absDens, habs]
      rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => Real.rpow_nonneg hδ.le _)]
      congr 1
      have e1 : ∏ i, (δ * x i) ^ k i = (∏ i, δ ^ k i) * ∏ i, x i ^ k i := by
        rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun i _ => mul_pow _ _ _
      have e2 : ∏ i, (δ * x i) ^ h i = (∏ i, δ ^ h i) * ∏ i, x i ^ h i := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => Real.mul_rpow hδ.le (hxi i).le
      rw [e1, e2]; ring_nf
    · rw [indicator_of_notMem (fun h' => hx (hmem.mp h')), indicator_of_notMem hx]
  simp_rw [hpt]
  rw [lintegral_indicator hC, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rfl

/-! ### The theorems -/

/-- The positive-orthant integral `Z₊(N) = ∫_{(0,δ]^d} e^{-N K} ∏ yᵢ^{hᵢ}` has the pair. -/
theorem hasLaplacePair_posBox {δ : ℝ} (hδ : 0 < δ) (k : Fin d → ℕ) (h : Fin d → ℝ)
    (hh : ∀ i, -1 < h i) (hS : ∃ i, k i ≠ 0) :
    HasLaplacePair (fun N => ∫⁻ y in posBox' δ, boxIntegrand k h N y) (ncLam k h) (ncMult k h) := by
  have hc : 0 < ∏ i, δ ^ k i := Finset.prod_pos fun i _ => pow_pos hδ _
  have ha : 0 < ∏ i, δ ^ h i := Finset.prod_pos fun i _ => Real.rpow_pos_of_pos hδ _
  have h1 := ((ncZ_hasLaplacePair k h hh hS).comp_mul hc).const_mul
    (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top
  have h2 : HasLaplacePair (fun N => ENNReal.ofReal (δ ^ d)⁻¹ *
      ∫⁻ y in posBox' δ, boxIntegrand k h N y) (ncLam k h) (ncMult k h) :=
    h1.congr (Eventually.of_forall fun N => (Z_pos_scale hδ k h N).symm)
  have h3 := h2.const_mul (a := ENNReal.ofReal (δ ^ d)) (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    ENNReal.ofReal_ne_top
  refine h3.congr (Eventually.of_forall fun N => ?_)
  simp only
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity),
    ENNReal.ofReal_one, one_mul]

/-- **Normal crossing on the box.** For `δ > 0`, `hᵢ > -1` and some `kᵢ ≠ 0`,
`∫_{[-δ,δ]^d} e^{-N ∏|yᵢ|^{kᵢ}} ∏|yᵢ|^{hᵢ} dy ≍ N^{-λ}(log N)^{m-1}` with
`λ = min {(hᵢ+1)/kᵢ : kᵢ ≠ 0}`, `m = #{i : kᵢ ≠ 0, (hᵢ+1)/kᵢ = λ}`. -/
theorem normalCrossing_box {δ : ℝ} (hδ : 0 < δ) (k : Fin d → ℕ) (h : Fin d → ℝ)
    (hh : ∀ i, -1 < h i) (hS : ∃ i, k i ≠ 0) :
    HasLaplacePair (Z (boxMeasure δ h) (absLoss k)) (ncLam k h) (ncMult k h) := by
  have hp := hasLaplacePair_posBox hδ k h hh hS
  have e : Z (boxMeasure δ h) (absLoss k) = fun N => ∫⁻ y in box δ, boxIntegrand k h N y :=
    funext (Z_boxMeasure δ k h)
  rw [e]
  refine ⟨hp.1, hp.2.1.mono (Eventually.of_forall fun N => Z_pos_le_box k h N), ?_⟩
  exact (hp.2.2.const_mul (ENNReal.natCast_ne_top _)).mono
    (Eventually.of_forall fun N => Z_box_le δ k h N)

/-- **Normal crossing on the box, with units.** A loss `K` with `c ∏|yᵢ|^{kᵢ} ≤ K ≤ C ∏|yᵢ|^{kᵢ}`
and a prior density `f` with `a ∏|yᵢ|^{hᵢ} ≤ f ≤ b ∏|yᵢ|^{hᵢ}` on the box (`0 < a, b, c, C`) give the
same pair. This is the shape of a resolution chart: `K ∘ g = unit × monomial`,
`φ(g) |det g'| = unit × monomial`. -/
theorem normalCrossing_box_units {δ : ℝ} (hδ : 0 < δ) (k : Fin d → ℕ) (h : Fin d → ℝ)
    (hh : ∀ i, -1 < h i) (hS : ∃ i, k i ≠ 0) {K : (Fin d → ℝ) → ℝ} {f : (Fin d → ℝ) → ℝ≥0∞}
    {a b c C : ℝ} (ha : 0 < a) (hc : 0 < c) (hC : 0 < C)
    (hKlo : ∀ y ∈ box δ, c * absLoss k y ≤ K y) (hKhi : ∀ y ∈ box δ, K y ≤ C * absLoss k y)
    (hflo : ∀ y ∈ box δ, ENNReal.ofReal a * ENNReal.ofReal (absDens h y) ≤ f y)
    (hfhi : ∀ y ∈ box δ, f y ≤ ENNReal.ofReal b * ENNReal.ofReal (absDens h y)) :
    HasLaplacePair (Z ((volume.restrict (box δ)).withDensity f) K) (ncLam k h) (ncMult k h) := by
  have hB := measurableSet_box (d := d) δ
  have hP := (normalCrossing_box hδ k h hh hS).of_prior (ν' := (volume.restrict (box δ)).withDensity f)
    (a := ENNReal.ofReal a) (b := ENNReal.ofReal b) (ENNReal.ofReal_pos.mpr ha).ne'
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    (by
      rw [boxMeasure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
      exact withDensity_mono ((ae_restrict_iff' hB).mpr (Eventually.of_forall hflo)))
    (by
      rw [boxMeasure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
      exact withDensity_mono ((ae_restrict_iff' hB).mpr (Eventually.of_forall hfhi)))
  have hac := withDensity_absolutelyContinuous (volume.restrict (box δ)) f
  exact hP.of_comparable hc hC (hac.ae_le ((ae_restrict_iff' hB).mpr (Eventually.of_forall hKlo)))
    (hac.ae_le ((ae_restrict_iff' hB).mpr (Eventually.of_forall hKhi)))

end SLT
