/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Upstream.Algebra
public import SLT.Pushforward.Linear
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Coordinates and linear changes of variables

* `lintegral_comp_formAct`: the substitution of forms rescales Lebesgue measure by `|det g|²`
  (a case of `SLT.Pushforward.lintegral_comp_complexLinear`);
* `measurePreserving_cubicEquiv`, `measurePreserving_rowEquiv`: Lebesgue measure on cubic space
  and on rows is the product measure in the coordinates `((P₀, P₁), (P₂, P₃))` and
  `((l₁, l₂), l₃)`;
* `volume_det2_eq_zero`: the pairs of forms with `det = 0` are Lebesgue-null.
-/

@[expose] public section

namespace SLT.PositionFour

open MeasureTheory Set SLT.Pushforward
open scoped ENNReal

/-- Lebesgue measure on `ℂ × ℂ` is an additive Haar measure. -/
instance isAddHaarMeasure_volume_form : (volume : Measure Form).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

/-- Lebesgue measure on `(ℂ × ℂ) × (ℂ × ℂ)` is an additive Haar measure. -/
instance isAddHaarMeasure_volume_pair : (volume : Measure (Form × Form)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

/-- The linear map `(u₁, u₂) ↦ (a u₁ + b u₂, c u₁ + d u₂)` on `ℂ × ℂ`. -/
noncomputable def lin2 (a b c d : ℂ) : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
  (LinearMap.fst ℂ ℂ ℂ).smulRight (a, c) + (LinearMap.snd ℂ ℂ ℂ).smulRight (b, d)

/-- `lin2` evaluated. -/
theorem lin2_apply (a b c d : ℂ) (u : ℂ × ℂ) :
    lin2 a b c d u = (a * u.1 + b * u.2, c * u.1 + d * u.2) := by
  simp [lin2, mul_comm]

/-- `det (lin2 a b c d) = a d - b c`. -/
theorem det_lin2 (a b c d : ℂ) : (lin2 a b c d).det = a * d - b * c := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℂ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, lin2_apply, Module.Basis.finTwoProd_zero,
    Module.Basis.finTwoProd_one]

/-- Substitution of forms `u ↦ u₁ l + u₂ m` as a complex-linear map. -/
theorem formAct_eq_lin2 (g : Form × Form) (u : Form) :
    formAct g u = lin2 g.1.1 g.2.1 g.1.2 g.2.2 u := by
  rw [lin2_apply, formAct]; ext <;> simp [mul_comm]

/-- **Substitution of forms.** `∫ F(u₁ l + u₂ m) du = |det g|⁻² ∫ F`. -/
theorem lintegral_comp_formAct (g : Form × Form) (hg : det2 g ≠ 0) {F : Form → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ u, F (formAct g u) = (ENNReal.ofReal (Complex.normSq (det2 g)))⁻¹ * ∫⁻ l, F l := by
  have hdet : (lin2 g.1.1 g.2.1 g.1.2 g.2.2).det = det2 g := by rw [det_lin2, det2]; ring
  simp_rw [formAct_eq_lin2]
  rw [lintegral_comp_complexLinear volume _ (by rwa [hdet]) hF, hdet]

/-! ### Product coordinates -/

/-- Cubic space in the coordinates `((P₀, P₁), (P₂, P₃))`, as an equivalence. -/
def cubicEquivFun : Cubic ≃ Form × Form where
  toFun P := ((P 0, P 1), (P 2, P 3))
  invFun g := ![g.1.1, g.1.2, g.2.1, g.2.2]
  left_inv P := by ext i; fin_cases i <;> rfl
  right_inv _ := rfl

/-- Cubic space in the coordinates `((P₀, P₁), (P₂, P₃))`. -/
def cubicEquiv : Cubic ≃ᵐ Form × Form where
  toEquiv := cubicEquivFun
  measurable_toFun := by
    change Measurable fun P : Cubic => ((P 0, P 1), (P 2, P 3))
    fun_prop
  measurable_invFun := by
    change Measurable fun g : Form × Form => (![g.1.1, g.1.2, g.2.1, g.2.2] : Cubic)
    refine measurable_pi_iff.mpr fun i => ?_
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, Fin.isValue] <;> fun_prop

/-- Rows in the coordinates `((l₁, l₂), l₃)`, as an equivalence. -/
def rowEquivFun : Row ≃ (Form × Form) × Form where
  toFun r := ((r 0, r 1), r 2)
  invFun g := ![g.1.1, g.1.2, g.2]
  left_inv r := by ext i <;> fin_cases i <;> rfl
  right_inv _ := rfl

/-- Rows in the coordinates `((l₁, l₂), l₃)`. -/
def rowEquiv : Row ≃ᵐ (Form × Form) × Form where
  toEquiv := rowEquivFun
  measurable_toFun := by
    change Measurable fun r : Row => ((r 0, r 1), r 2)
    fun_prop
  measurable_invFun := by
    change Measurable fun g : (Form × Form) × Form => (![g.1.1, g.1.2, g.2] : Row)
    refine measurable_pi_iff.mpr fun i => ?_
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, Fin.isValue] <;> fun_prop

/-- `cubicEquiv` evaluated. -/
@[simp] theorem cubicEquiv_apply (P : Cubic) : cubicEquiv P = ((P 0, P 1), (P 2, P 3)) := rfl

/-- `cubicEquiv.symm` evaluated. -/
@[simp] theorem cubicEquiv_symm_apply (g : Form × Form) :
    cubicEquiv.symm g = ![g.1.1, g.1.2, g.2.1, g.2.2] := rfl

/-- `rowEquiv` evaluated. -/
@[simp] theorem rowEquiv_apply (r : Row) : rowEquiv r = ((r 0, r 1), r 2) := rfl

/-- `rowEquiv.symm` evaluated. -/
@[simp] theorem rowEquiv_symm_apply (g : (Form × Form) × Form) :
    rowEquiv.symm g = ![g.1.1, g.1.2, g.2] := rfl

/-- Lebesgue measure on cubic space is the product measure in `((P₀, P₁), (P₂, P₃))`. -/
theorem measurePreserving_cubicEquiv : MeasurePreserving cubicEquiv := by
  have h : MeasurePreserving cubicEquiv.symm := by
    refine ⟨cubicEquiv.symm.measurable, ?_⟩
    rw [volume_pi]
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [MeasurableEquiv.map_apply]
    have : cubicEquiv.symm ⁻¹' univ.pi s = (s 0 ×ˢ s 1) ×ˢ (s 2 ×ˢ s 3) := by
      ext g
      simp only [mem_preimage, mem_univ_pi, mem_prod]
      constructor
      · intro h; exact ⟨⟨h 0, h 1⟩, ⟨h 2, h 3⟩⟩
      · rintro ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩ i
        fin_cases i
        exacts [h0, h1, h2, h3]
    rw [this, Measure.volume_eq_prod Form Form, Measure.prod_prod, Measure.volume_eq_prod ℂ ℂ,
      Measure.prod_prod, Measure.prod_prod, Fin.prod_univ_four]
    ring
  simpa using h.symm

/-- Lebesgue measure on rows is the product measure in `((l₁, l₂), l₃)`. -/
theorem measurePreserving_rowEquiv : MeasurePreserving rowEquiv := by
  have h : MeasurePreserving rowEquiv.symm := by
    refine ⟨rowEquiv.symm.measurable, ?_⟩
    rw [volume_pi]
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [MeasurableEquiv.map_apply]
    have : rowEquiv.symm ⁻¹' univ.pi s = (s 0 ×ˢ s 1) ×ˢ s 2 := by
      ext g
      simp only [mem_preimage, mem_univ_pi, mem_prod]
      constructor
      · intro h; exact ⟨⟨h 0, h 1⟩, h 2⟩
      · rintro ⟨⟨h0, h1⟩, h2⟩ i
        fin_cases i
        exacts [h0, h1, h2]
    rw [this, Measure.volume_eq_prod (Form × Form) Form, Measure.prod_prod,
      Measure.volume_eq_prod Form Form, Measure.prod_prod, Fin.prod_univ_three]
  simpa using h.symm

/-! ### Null sets -/

/-- The pairs of forms with `det(l, m) = 0` form a Lebesgue-null set. -/
theorem volume_det2_eq_zero : volume {g : Form × Form | det2 g = 0} = 0 := by
  have hmeas : ∀ l : Form, MeasurableSet {m : Form | l.1 * m.2 - l.2 * m.1 = 0} := fun l =>
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hinner : ∀ l : Form, l ≠ 0 → volume {m : Form | l.1 * m.2 - l.2 * m.1 = 0} = 0 := by
    intro l hl
    rw [Measure.volume_eq_prod, Measure.measure_prod_null (hmeas l)]
    filter_upwards [Measure.ae_ne (volume : Measure ℂ) 0] with c hc
    simp only [Pi.zero_apply]
    refine Set.Subsingleton.measure_zero ?_ _
    intro d₁ hd₁ d₂ hd₂
    simp only [mem_preimage, mem_ofPred_eq] at hd₁ hd₂
    have hc0 : c ≠ 0 := hc
    by_cases ha : l.1 = 0
    · exfalso
      have hb : l.2 ≠ 0 := fun hb => hl (Prod.ext ha hb)
      rw [ha, zero_mul, zero_sub, neg_eq_zero] at hd₁
      exact mul_ne_zero hb hc0 hd₁
    · have : l.1 * (d₁ - d₂) = 0 := by linear_combination hd₁ - hd₂
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha)
  have hS : MeasurableSet {g : Form × Form | det2 g = 0} :=
    measurableSet_eq_fun (by unfold det2; fun_prop) measurable_const
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hS]
  filter_upwards [Measure.ae_ne (volume : Measure Form) 0] with l hl
  exact hinner l hl

end SLT.PositionFour
