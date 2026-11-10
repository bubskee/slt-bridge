/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Change of variables with bounded multiplicity

Mathlib's change of variables `lintegral_image_eq_lintegral_abs_det_fderiv_mul` needs an injective
map. The note's pushforwards go through maps of degree `18`, `3` and `2`. This file proves the two
inequalities that replace injectivity, for a map `f : E → E` differentiable on a measurable set `s`
with invertible derivative there:

* `lintegral_abs_det_fderiv_mul_le`: if every fibre of `f` on `s` has at most `N` points, then
  `∫_s |det f'| · g ∘ f ≤ N ∫ g` (the pushforward of `|det f'| dx` has density at most `N`);
* `lintegral_image_le_lintegral_abs_det_fderiv_mul`: `∫_{f(s)} g ≤ ∫_s |det f'| · g ∘ f`
  (a covering inequality, no fibre bound needed).

Both come from one countable partition of `s` into pieces on which `f` is injective
(`exists_injOn_partition`), built from Mathlib's partition into pieces where `f` is close to a
linear map.
-/

@[expose] public section

namespace SLT.PositionFour

open MeasureTheory Set Function
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A radius below which a map close to `A` is injective, when `A` is invertible. -/
noncomputable def injRadius (A : E →L[ℝ] E) : ℝ≥0 :=
  if h : A.det ≠ 0 then
    (‖((A.toContinuousLinearEquivOfDetNeZero h).symm : E →L[ℝ] E)‖₊ + 1)⁻¹ / 2
  else 1

/-- The injectivity radius is positive. -/
theorem injRadius_ne_zero (A : E →L[ℝ] E) : injRadius A ≠ 0 := by
  unfold injRadius
  split_ifs <;> simp

variable [MeasurableSpace E] [BorelSpace E]

/-- **Injective partition.** A map with invertible derivative on `s` is injective on each piece of
a countable measurable partition of `s`. -/
theorem exists_injOn_partition [Nontrivial E] {f : E → E} {s : Set E} {f' : E → E →L[ℝ] E}
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hdet : ∀ x ∈ s, (f' x).det ≠ 0) :
    ∃ t : ℕ → Set E, Pairwise (Disjoint on t) ∧ (∀ n, MeasurableSet (t n)) ∧
      s ⊆ ⋃ n, t n ∧ ∀ n, InjOn f (s ∩ t n) := by
  obtain ⟨t, A, ht, htm, hst, hA, hAs⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' injRadius
      injRadius_ne_zero
  refine ⟨t, ht, htm, hst, fun n => ?_⟩
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hs]
  obtain ⟨y, hy, hAy⟩ := hAs hs n
  have hdA : (A n).det ≠ 0 := hAy ▸ hdet y hy
  set e := (A n).toContinuousLinearEquivOfDetNeZero hdA with he_def
  have he : (e : E →L[ℝ] E) = A n := ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
  have happrox : ApproximatesLinearOn f (e : E →L[ℝ] E) (s ∩ t n) (injRadius (A n)) := by
    rw [he]; exact hA n
  refine happrox.injOn (Or.inr ?_)
  have hN : 0 < ‖(e.symm : E →L[ℝ] E)‖₊ := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    refine pos_iff_ne_zero.mpr fun h0 => ?_
    have : (e.symm : E →L[ℝ] E) = 0 := nnnorm_eq_zero.mp h0
    apply hx
    have h1 : e.symm (e x) = 0 := by
      rw [show e.symm (e x) = (e.symm : E →L[ℝ] E) (e x) from rfl, this]; rfl
    simpa using h1
  have hr : injRadius (A n) = (‖(e.symm : E →L[ℝ] E)‖₊ + 1)⁻¹ / 2 := by
    simp [injRadius, hdA, he_def]
  rw [hr]
  calc (‖(e.symm : E →L[ℝ] E)‖₊ + 1)⁻¹ / 2 ≤ (‖(e.symm : E →L[ℝ] E)‖₊ + 1)⁻¹ :=
        half_le_self zero_le
    _ < ‖(e.symm : E →L[ℝ] E)‖₊⁻¹ := by
        exact (inv_lt_inv₀ (by positivity) hN).mpr (lt_add_one _)

variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The partition of `exists_injOn_partition`, restricted to `s`, with the facts used below. -/
theorem exists_injOn_pieces [Nontrivial E] {f : E → E} {s : Set E} {f' : E → E →L[ℝ] E}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hdet : ∀ x ∈ s, (f' x).det ≠ 0) :
    ∃ S : ℕ → Set E, (∀ n, MeasurableSet (S n)) ∧ Pairwise (Disjoint on S) ∧ ⋃ n, S n = s ∧
      (∀ n, S n ⊆ s) ∧ (∀ n, InjOn f (S n)) ∧
      ∀ n, ∀ x ∈ S n, HasFDerivWithinAt f (f' x) (S n) x := by
  obtain ⟨t, ht, htm, hst, hinj⟩ := exists_injOn_partition hf' hdet
  refine ⟨fun n => s ∩ t n, fun n => hs.inter (htm n), fun i j hij =>
    (ht hij).mono inter_subset_right inter_subset_right, ?_, fun n => inter_subset_left, hinj,
    fun n x hx => (hf' x hx.1).mono inter_subset_left⟩
  ext x
  simp only [mem_iUnion, mem_inter_iff]
  exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => by
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hst hx); exact ⟨n, hx, hn⟩⟩

/-- **Bounded multiplicity.** If `f` has invertible derivative on `s` and every fibre of `f` on
`s` has at most `N` points, then `∫_s |det f'| · g ∘ f ≤ N ∫ g`. -/
theorem lintegral_abs_det_fderiv_mul_le [Nontrivial E] {f : E → E} {s : Set E}
    {f' : E → E →L[ℝ] E} (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hdet : ∀ x ∈ s, (f' x).det ≠ 0) {N : ℕ}
    (hN : ∀ y, ∃ F : Finset E, F.card ≤ N ∧ ∀ x ∈ s, f x = y → x ∈ F)
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ ≤ N * ∫⁻ y, g y ∂μ := by
  classical
  obtain ⟨S, hSm, hSd, hSu, hSs, hinj, hSf⟩ := exists_injOn_pieces hs hf' hdet
  have himm : ∀ n, MeasurableSet (f '' S n) := fun n =>
    measurable_image_of_fderivWithin (hSm n) (hSf n) (hinj n)
  -- at most `N` pieces have `y` in their image
  have hcount : ∀ y, ∑' n, (f '' S n).indicator (1 : E → ℝ≥0∞) y ≤ N := by
    intro y
    obtain ⟨F, hF, hFy⟩ := hN y
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun T => ?_
    have hsum : ∑ n ∈ T, (f '' S n).indicator (1 : E → ℝ≥0∞) y =
        ((T.filter fun n => y ∈ f '' S n).card : ℝ≥0∞) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases h : y ∈ f '' S n <;> simp [h]
    rw [hsum, Nat.cast_le]
    refine le_trans ?_ hF
    let φ : ℕ → E := fun n => if h : y ∈ f '' S n then h.choose else 0
    have hφ : ∀ n, y ∈ f '' S n → φ n ∈ S n ∧ f (φ n) = y := by
      intro n h
      simp only [φ, h, dite_true]
      exact h.choose_spec
    refine Finset.card_le_card_of_injOn φ (fun n hn => ?_) (fun n hn m hm hnm => ?_)
    · have hn' := (Finset.mem_filter.mp hn).2
      exact hFy _ (hSs n (hφ n hn').1) (hφ n hn').2
    · have hn' := (hφ n (Finset.mem_filter.mp hn).2).1
      have hm' := (hφ m (Finset.mem_filter.mp hm).2).1
      by_contra hne
      exact Set.disjoint_left.mp (hSd hne) hn' (hnm ▸ hm')
  calc ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ
      = ∑' n, ∫⁻ x in S n, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ := by
        conv_lhs => rw [← hSu]
        exact lintegral_iUnion hSm hSd _
    _ = ∑' n, ∫⁻ y, (f '' S n).indicator g y ∂μ := by
        congr 1; funext n
        rw [lintegral_indicator (himm n),
          lintegral_image_eq_lintegral_abs_det_fderiv_mul μ (hSm n) (hSf n) (hinj n)]
    _ = ∫⁻ y, ∑' n, (f '' S n).indicator g y ∂μ :=
        (lintegral_tsum fun n => (hg.indicator (himm n)).aemeasurable).symm
    _ ≤ ∫⁻ y, N * g y ∂μ := by
        refine lintegral_mono fun y => ?_
        have : ∀ n, (f '' S n).indicator g y = (f '' S n).indicator (1 : E → ℝ≥0∞) y * g y :=
          fun n => by by_cases h : y ∈ f '' S n <;> simp [h]
        simp_rw [this]
        rw [ENNReal.tsum_mul_right]
        exact mul_le_mul_left (hcount y) _
    _ = N * ∫⁻ y, g y ∂μ := lintegral_const_mul _ hg

/-- **Covering inequality.** If `f` has invertible derivative on `s`, then
`∫_{f(s)} g ≤ ∫_s |det f'| · g ∘ f`. -/
theorem lintegral_image_le_lintegral_abs_det_fderiv_mul [Nontrivial E] {f : E → E} {s : Set E}
    {f' : E → E →L[ℝ] E} (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hdet : ∀ x ∈ s, (f' x).det ≠ 0) (g : E → ℝ≥0∞) :
    ∫⁻ y in f '' s, g y ∂μ ≤ ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ := by
  obtain ⟨S, hSm, hSd, hSu, -, hinj, hSf⟩ := exists_injOn_pieces hs hf' hdet
  calc ∫⁻ y in f '' s, g y ∂μ = ∫⁻ y in ⋃ n, f '' S n, g y ∂μ := by rw [← image_iUnion, hSu]
    _ ≤ ∑' n, ∫⁻ y in f '' S n, g y ∂μ := lintegral_iUnion_le _ _
    _ = ∑' n, ∫⁻ x in S n, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ := by
        congr 1; funext n
        exact lintegral_image_eq_lintegral_abs_det_fderiv_mul μ (hSm n) (hSf n) (hinj n) g
    _ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ := by
        conv_rhs => rw [← hSu]
        exact (lintegral_iUnion hSm hSd _).symm

end SLT.PositionFour
