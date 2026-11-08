/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Zoo.MLPArrangement

/-!
# Zoo: the mixed identity group `J(1, 1) = (7/12, 1)` (resnet-bridge Lemma R0.2)

Source: resnet-bridge `readwrite/R0_scalar.md` at `c55350b`, Lemma R0.2 (AI-reviewed; read only,
not a dependency). With `w ∈ ℝ^p`, `y ∈ ℝ^q`, `S = Σ wᵢ³ + Σ yⱼ` and `Q = Σ wᵢ⁶ + Σ yⱼ²`, it claims
`∫ e^{-N(S² + Q²)} ≍ N^{-λ}` with `J(p, q) = (1/2 + p/12 + (q−1)/4, 1)`. Here the case
`p = q = 1` is **Lean-certified**, on every box `[-δ, δ]²` with `δ ≤ 1/2`:

  `mixedLoss (w, y) = (w³ + y)² + (w⁶ + y²)²` has pair `J(1, 1) = (7/12, 1)` (`mixedGroup_pair`).

**Why this is not a direct N2 instance.** In `(w, y)` the loss is not comparable to any monomial
sum. At `(w, -w³)` it is `4w¹²`, and at `(w, w³)` it is `≍ 4w⁶`, while a monomial sum only sees
`|y|` (`docs/T5_R02_note.md` §1). The cancellation in `S` is removed by the source's own change of
coordinates `y = s − w³` (`shear`). That map is triangular with unit Jacobian (not linear, as the
source says), so it preserves Lebesgue measure (`measurePreserving_shear`). In `(w, s)` the loss is
`shearLoss = s² + (w⁶ + (s − w³)²)² ≍ s² + w¹²`, a pure-power sum. N2 (through
`SLT.Zoo.MLP.pair_of_powΓ`) gives `(1/12 + 1/2, 1)`.

**The box.** The shear does not map boxes to boxes. Its preimage of `[-δ, δ]²` is sandwiched between
`[-δ/2, δ/2]²` and `[-2δ, 2δ]²` (`box_half_subset`, `preimage_subset_box_two`). Both boxes give the
same pair, so the original box does too (`HasLaplacePair.squeeze`).

General `(p, q)` is not built. It is the same argument with `Fin.append` bookkeeping.
-/

@[expose] public section

namespace SLT.Zoo.MixedGroup

open MeasureTheory Set SLT SLT.Newton SLT.NC
open SLT.Zoo.MLP (pair_of_powΓ)
open scoped ENNReal

/-- **Squeeze**: a function between two functions with the same pair has that pair. -/
theorem HasLaplacePair.squeeze {F G H : ℝ → ℝ≥0∞} {lam : ℝ} {m : ℕ}
    (hG : HasLaplacePair G lam m) (hH : HasLaplacePair H lam m) (hGF : ∀ N, G N ≤ F N)
    (hFH : ∀ N, F N ≤ H N) : HasLaplacePair F lam m :=
  ⟨hG.1, hG.2.1.mono (Filter.Eventually.of_forall hGF),
    hH.2.2.mono (Filter.Eventually.of_forall hFH)⟩

/-- R0.2's loss for `p = q = 1`, in `(w, y) = (x 0, x 1)`: `S² + Q²` with `S = w³ + y`,
`Q = w⁶ + y²`. -/
def mixedLoss (x : Fin 2 → ℝ) : ℝ := (x 0 ^ 3 + x 1) ^ 2 + (x 0 ^ 6 + x 1 ^ 2) ^ 2

/-- The same loss in the sheared coordinates `(w, s) = (x 0, x 1)`, `s = S`. -/
def shearLoss (x : Fin 2 → ℝ) : ℝ := x 1 ^ 2 + (x 0 ^ 6 + (x 1 - x 0 ^ 3) ^ 2) ^ 2

/-- The shear `(w, s) ↦ (w, s − w³)`, i.e. `y = S − w³`. -/
def shear (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![x 0, x 1 - x 0 ^ 3]

/-- In sheared coordinates the loss is `shearLoss`. -/
theorem mixedLoss_shear (x : Fin 2 → ℝ) : mixedLoss (shear x) = shearLoss x := by
  simp only [mixedLoss, shear, shearLoss, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-- The sheared loss is measurable. -/
theorem measurable_shearLoss : Measurable shearLoss := by
  unfold shearLoss; fun_prop

/-- The mixed-group loss is measurable. -/
theorem measurable_mixedLoss : Measurable mixedLoss := by
  unfold mixedLoss; fun_prop

/-- The shear as a measurable equivalence, with inverse `(w, y) ↦ (w, y + w³)`. -/
noncomputable def shearEquiv : (Fin 2 → ℝ) ≃ᵐ (Fin 2 → ℝ) where
  toFun := shear
  invFun x := ![x 0, x 1 + x 0 ^ 3]
  left_inv x := by funext i; fin_cases i <;> simp [shear]
  right_inv x := by funext i; fin_cases i <;> simp [shear]
  measurable_toFun := by
    refine measurable_pi_iff.mpr fun i => ?_
    fin_cases i
    · exact measurable_pi_apply 0
    · exact (measurable_pi_apply 1).sub ((measurable_pi_apply 0).pow_const 3)
  measurable_invFun := by
    refine measurable_pi_iff.mpr fun i => ?_
    fin_cases i
    · exact measurable_pi_apply 0
    · exact (measurable_pi_apply 1).add ((measurable_pi_apply 0).pow_const 3)

/-- **The shear preserves Lebesgue measure** (Fubini: a translation in the second coordinate by an
amount depending on the first). -/
theorem measurePreserving_shear : MeasurePreserving shear volume volume := by
  have h1 := volume_preserving_finTwoArrow ℝ
  have h2 : MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.2 - p.1 ^ 3))
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) :=
    (MeasurePreserving.id volume).skew_product (g := fun a b => b - a ^ 3) (by fun_prop)
      (Filter.Eventually.of_forall fun a => (measurePreserving_sub_right volume (a ^ 3)).map_eq)
  rw [← Measure.volume_eq_prod] at h2
  have h3 := (h1.symm MeasurableEquiv.finTwoArrow).comp (h2.comp h1)
  convert h3 using 1
  funext x i
  fin_cases i <;> simp [shear]

/-- The free energy of `mixedLoss` on a box equals that of `shearLoss` on the shear's preimage. -/
theorem Z_mixed_eq_shear (δ : ℝ) :
    Z (volume.restrict (box δ)) mixedLoss = Z (volume.restrict (shear ⁻¹' box δ)) shearLoss := by
  funext N
  simp only [Z]
  have e := measurePreserving_shear.setLIntegral_comp_preimage_emb
    (shearEquiv.measurableEmbedding : MeasurableEmbedding shear)
    (fun y => ENNReal.ofReal (Real.exp (-(N * mixedLoss y)))) (box δ)
  simp only [mixedLoss_shear] at e
  exact e.symm

/-! ### The box sandwich -/

private theorem mem_box_two {δ : ℝ} {x : Fin 2 → ℝ} :
    x ∈ box δ ↔ |x 0| ≤ δ ∧ |x 1| ≤ δ := by
  simp only [box, mem_univ_pi, Fin.forall_fin_two, mem_Icc, abs_le]

private theorem abs_cube_le {t δ : ℝ} (ht : |t| ≤ δ) : |t ^ 3| ≤ δ ^ 3 := by
  rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg t) ht 3

/-- `[-δ/2, δ/2]² ⊆ shear⁻¹ [-δ, δ]²` for `0 < δ ≤ 1/2`. -/
theorem box_half_subset {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    box (δ / 2) ⊆ shear ⁻¹' box δ := by
  intro x hx
  rw [mem_box_two] at hx
  rw [mem_preimage, mem_box_two]
  simp only [shear, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hc := abs_cube_le hx.1
  have hδ3 : (δ / 2) ^ 3 ≤ δ / 2 := by
    have : (δ / 2) ^ 2 ≤ 1 := by nlinarith
    nlinarith [pow_two_nonneg (δ / 2)]
  refine ⟨by linarith [hx.1], ?_⟩
  calc |x 1 - x 0 ^ 3| ≤ |x 1| + |x 0 ^ 3| := abs_sub _ _
    _ ≤ δ / 2 + δ / 2 := by linarith [hx.2]
    _ = δ := by ring

/-- `shear⁻¹ [-δ, δ]² ⊆ [-2δ, 2δ]²` for `0 < δ ≤ 1`. -/
theorem preimage_subset_box_two {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    shear ⁻¹' box δ ⊆ box (2 * δ) := by
  intro x hx
  rw [mem_preimage, mem_box_two] at hx
  simp only [shear, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hx
  rw [mem_box_two]
  have hc := abs_cube_le hx.1
  have hδ3 : δ ^ 3 ≤ δ := by nlinarith [pow_two_nonneg δ]
  refine ⟨by linarith [hx.1], ?_⟩
  calc |x 1| = |(x 1 - x 0 ^ 3) + x 0 ^ 3| := by ring_nf
    _ ≤ |x 1 - x 0 ^ 3| + |x 0 ^ 3| := abs_add_le _ _
    _ ≤ 2 * δ := by linarith [hx.2]

/-! ### The sheared loss is pure-power -/

private theorem abs_rpow_even {t : ℝ} {n : ℕ} (hn : Even n) : |t| ^ (n : ℝ) = t ^ n := by
  rw [Real.rpow_natCast, hn.pow_abs]

/-- **On `[-ρ, ρ]²` with `ρ ≤ 1`, `shearLoss ≍ w¹² + s²`**, so its pair is `(1/12 + 1/2, 1)`. -/
theorem shearLoss_pair {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    HasLaplacePair (Z (volume.restrict (box ρ)) shearLoss) (7 / 12) 1 := by
  have h := pair_of_powΓ (s := Finset.univ) (k := ![12, 2]) Finset.univ_nonempty
    (fun i _ => by fin_cases i <;> norm_num) hρ measurable_shearLoss (c := 1) (C := 18) one_pos
    (fun x _ => ?_) (fun x hx => ?_)
  · convert h using 1; simp [Fin.sum_univ_two]; norm_num
  all_goals simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, shearLoss]
  all_goals rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, abs_rpow_even (by decide), abs_rpow_even (by decide)]
  · have ha := pow_two_nonneg (x 0 ^ 3)
    have hb := pow_two_nonneg (x 1 - x 0 ^ 3)
    nlinarith [mul_nonneg ha hb, pow_two_nonneg (x 1 - x 0 ^ 3)]
  · have h1 : x 1 ^ 2 ≤ 1 := by
      have := (mem_box_two.mp hx).2
      rw [← sq_abs]; nlinarith [abs_nonneg (x 1)]
    have hQ : x 0 ^ 6 + (x 1 - x 0 ^ 3) ^ 2 ≤ 3 * x 0 ^ 6 + 2 * x 1 ^ 2 := by
      nlinarith [sq_nonneg (x 1 + x 0 ^ 3)]
    have hQ0 : 0 ≤ x 0 ^ 6 + (x 1 - x 0 ^ 3) ^ 2 := by positivity
    have hQ2 : (x 0 ^ 6 + (x 1 - x 0 ^ 3) ^ 2) ^ 2 ≤ (3 * x 0 ^ 6 + 2 * x 1 ^ 2) ^ 2 :=
      pow_le_pow_left₀ hQ0 hQ 2
    have h4 : x 1 ^ 4 ≤ x 1 ^ 2 := by nlinarith [pow_two_nonneg (x 1)]
    nlinarith [sq_nonneg (3 * x 0 ^ 6 - 2 * x 1 ^ 2), pow_two_nonneg (x 0 ^ 6)]

/-- **R0.2 for `p = q = 1`, Lean-certified: `J(1, 1) = (7/12, 1)`.** On every box `[-δ, δ]²` with
`0 < δ ≤ 1/2`, `∫ e^{-N((w³ + y)² + (w⁶ + y²)²)} ≍ N^{-7/12}`, with no logarithm. -/
theorem mixedGroup_pair {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    HasLaplacePair (Z (volume.restrict (box δ)) mixedLoss) (7 / 12) 1 := by
  rw [Z_mixed_eq_shear]
  refine HasLaplacePair.squeeze (shearLoss_pair (ρ := δ / 2) (by positivity) (by linarith))
    (shearLoss_pair (ρ := 2 * δ) (by positivity) (by linarith)) (fun N => ?_) (fun N => ?_)
  · exact Z_mono_measure (Measure.restrict_mono (box_half_subset hδ hδ') le_rfl)
  · exact Z_mono_measure (Measure.restrict_mono (preimage_subset_box_two hδ (by linarith)) le_rfl)

/-- The pair matches the source's formula `J(p, q) = (1/2 + p/12 + (q−1)/4, 1)` at `p = q = 1`. -/
theorem mixedGroup_pair_formula {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    HasLaplacePair (Z (volume.restrict (box δ)) mixedLoss)
      (1 / 2 + (1 : ℝ) / 12 + ((1 : ℝ) - 1) / 4) 1 := by
  convert mixedGroup_pair hδ hδ' using 1; norm_num

end SLT.Zoo.MixedGroup
