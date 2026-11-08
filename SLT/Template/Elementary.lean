/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Laplace.Pair
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The elementary template, part 1: weak-L¹ weights (brief 03, T1)

The elementary route to an upper bound (cubic-chaos Theorem M, Proposition L′) never resolves
singularities. It bounds the free energy fibre by fibre:

* **slice bound**: at a frozen base point `x`, the fibre integral is at most
  `min (T, s(N) · w x)`. Here `T` is a trivial bound (the fibre volume), `s(N)` is a rate in `N`
  that is uniform in `x`, and `w` is a singular weight (in Theorem M,
  `w = r⁻³ |det|^{-1/2}`);
* **integrability of the weight**: if `w` is integrable, integrating over `x` keeps the rate.
  If `w` is only **weak-L¹** (`ρ {w > t} ≤ B / t`), integrating over `x` costs one extra
  `log N`.

This file proves the weak-L¹ step in general (`lintegral_min_le_of_weakL1`), with explicit
constants, by the layer cake formula. `SLT/Template/Cone.lean` shows where weak-L¹ comes from: a
weight of critical homogeneity on a cone whose angular part is integrable. `SLT/Template/Fibre.lean`
assembles the fibre theorems.
-/

@[expose] public section

namespace SLT.Template

open MeasureTheory Set Real
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- `w` is **weak-L¹** with constant `B`: `ρ {x | t < w x} ≤ B / t` for every `t > 0`. -/
def WeakL1 (ρ : Measure X) (w : X → ℝ≥0∞) (B : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ρ {x | ENNReal.ofReal t < w x} ≤ ENNReal.ofReal (B / t)

/-- An integrable weight is weak-L¹ (Markov). -/
theorem weakL1_of_lintegral_le {ρ : Measure X} {w : X → ℝ≥0∞} (hw : AEMeasurable w ρ) {B : ℝ}
    (hB : ∫⁻ x, w x ∂ρ ≤ ENNReal.ofReal B) : WeakL1 ρ w B := by
  intro t ht
  calc ρ {x | ENNReal.ofReal t < w x} ≤ ρ {x | ENNReal.ofReal t ≤ w x} :=
        measure_mono fun x hx => by simp only [mem_ofPred_eq] at hx ⊢; exact hx.le
    _ ≤ (∫⁻ x, w x ∂ρ) / ENNReal.ofReal t :=
        meas_ge_le_lintegral_div hw (by simpa using ht) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal B / ENNReal.ofReal t := by gcongr
    _ = ENNReal.ofReal (B / t) := by
        rcases le_or_gt B 0 with hB0 | hB0
        · rw [ENNReal.ofReal_of_nonpos hB0, ENNReal.zero_div,
            ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg hB0 ht.le)]
        · rw [ENNReal.ofReal_div_of_pos ht]

/-- The 1-D integral `∫_{(a,T]} c/t dt = c log(T/a)`, as a lintegral. -/
theorem lintegral_Ioc_div {a T c : ℝ} (ha : 0 < a) (haT : a ≤ T) (hc : 0 ≤ c) :
    ∫⁻ t in Ioc a T, ENNReal.ofReal (c / t) = ENNReal.ofReal (c * Real.log (T / a)) := by
  have hint : IntegrableOn (fun t : ℝ => c / t) (Ioc a T) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact continuousOn_const.div continuousOn_id fun t ht => (ha.trans_le ht.1).ne'
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · rw [← intervalIntegral.integral_of_le haT]
    simp_rw [div_eq_mul_inv c]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha (ha.trans_le haT)]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact div_nonneg hc (ha.trans ht.1).le

/-- **Weak-L¹ costs one log.** If `w` is weak-L¹ with constant `B` and `ρ` has mass at most `V`,
then for `T, s > 0`

`∫ min (T, s · w) dρ ≤ s · (V + B · log⁺ (T / s))`. -/
theorem lintegral_min_le_of_weakL1 {ρ : Measure X} {w : X → ℝ≥0∞} (hw : AEMeasurable w ρ)
    {B V T s : ℝ} (hB : 0 ≤ B) (hV0 : 0 ≤ V) (hV : ρ univ ≤ ENNReal.ofReal V)
    (hBw : WeakL1 ρ w B)
    (hT : 0 < T) (hs : 0 < s) :
    ∫⁻ x, min (ENNReal.ofReal T) (ENNReal.ofReal s * w x) ∂ρ ≤
      ENNReal.ofReal (s * (V + B * Real.posLog (T / s))) := by
  set g : X → ℝ≥0∞ := fun x => min (ENNReal.ofReal T) (ENNReal.ofReal s * w x) with hg
  have hgT : ∀ x, g x ≤ ENNReal.ofReal T := fun x => min_le_left _ _
  have hgne : ∀ x, g x ≠ ⊤ := fun x => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hgT x)
  set f : X → ℝ := fun x => (g x).toReal with hf
  have hgf : ∀ x, g x = ENNReal.ofReal (f x) := fun x => (ENNReal.ofReal_toReal (hgne x)).symm
  have hfm : AEMeasurable f ρ :=
    (aemeasurable_const.min (aemeasurable_const.mul hw)).ennreal_toReal
  have hfT : ∀ x, f x ≤ T := fun x => by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hgT x)
    rwa [ENNReal.toReal_ofReal hT.le] at this
  -- the distribution of `f`
  have hdist : ∀ t ∈ Ioi (0 : ℝ), ρ {x | t < f x} ≤
      (Iio T).indicator (fun t => min (ENNReal.ofReal V) (ENNReal.ofReal (B * s / t))) t := by
    intro t ht
    by_cases htT : t < T
    · rw [indicator_of_mem (show t ∈ Iio T from htT)]
      refine le_min ((measure_mono (subset_univ _)).trans hV) ?_
      have hsub : {x | t < f x} ⊆ {x | ENNReal.ofReal (t / s) < w x} := by
        intro x hx
        simp only [mem_ofPred_eq] at hx ⊢
        have h1 : ENNReal.ofReal t < g x := by
          rw [hgf]; exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt ht)).mpr hx
        have h2 : ENNReal.ofReal t < ENNReal.ofReal s * w x := h1.trans_le (min_le_right _ _)
        rw [ENNReal.ofReal_div_of_pos hs]
        exact ENNReal.div_lt_of_lt_mul' h2
      refine (measure_mono hsub).trans ((hBw _ (div_pos ht hs)).trans (le_of_eq ?_))
      congr 1
      field_simp
    · rw [indicator_of_notMem (show t ∉ Iio T from htT)]
      have : {x | t < f x} = ∅ := by
        ext x
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        exact (hfT x).trans (not_lt.mp htT)
      rw [this, measure_empty]
  -- the 1-D integral
  set a := min T s with ha
  have ha0 : 0 < a := lt_min hT hs
  have haT : a ≤ T := min_le_left _ _
  have has : a ≤ s := min_le_right _ _
  have hlog : Real.log (T / a) ≤ Real.posLog (T / s) := by
    rcases le_total s T with h | h
    · rw [ha, min_eq_right h, Real.posLog_eq_log (by
        rw [abs_of_pos (div_pos hT hs)]; exact (one_le_div hs).mpr h)]
    · rw [ha, min_eq_left h, div_self hT.ne', Real.log_one]; exact Real.posLog_nonneg
  have h1D : ∫⁻ t in Ioi (0 : ℝ),
      (Iio T).indicator (fun t => min (ENNReal.ofReal V) (ENNReal.ofReal (B * s / t))) t ≤
      ENNReal.ofReal (V * a) + ENNReal.ofReal (B * s * Real.log (T / a)) := by
    have hsplit : ∀ t ∈ Ioi (0 : ℝ),
        (Iio T).indicator (fun t => min (ENNReal.ofReal V) (ENNReal.ofReal (B * s / t))) t ≤
          (Ioc 0 a).indicator (fun _ => ENNReal.ofReal V) t +
            (Ioc a T).indicator (fun t => ENNReal.ofReal (B * s / t)) t := by
      intro t ht
      by_cases htT : t < T
      · rw [indicator_of_mem (show t ∈ Iio T from htT)]
        by_cases hta : t ≤ a
        · rw [indicator_of_mem (show t ∈ Ioc 0 a from ⟨ht, hta⟩)]
          exact (min_le_left _ _).trans le_self_add
        · rw [indicator_of_mem (show t ∈ Ioc a T from ⟨not_le.mp hta, htT.le⟩)]
          exact (min_le_right _ _).trans le_add_self
      · rw [indicator_of_notMem (show t ∉ Iio T from htT)]; exact zero_le
    calc _ ≤ ∫⁻ t in Ioi (0 : ℝ), ((Ioc 0 a).indicator (fun _ => ENNReal.ofReal V) t +
            (Ioc a T).indicator (fun t => ENNReal.ofReal (B * s / t)) t) :=
          setLIntegral_mono' measurableSet_Ioi hsplit
      _ ≤ ∫⁻ t, ((Ioc 0 a).indicator (fun _ => ENNReal.ofReal V) t +
            (Ioc a T).indicator (fun t => ENNReal.ofReal (B * s / t)) t) :=
          setLIntegral_le_lintegral _ _
      _ = (∫⁻ t, (Ioc 0 a).indicator (fun _ => ENNReal.ofReal V) t) +
            ∫⁻ t, (Ioc a T).indicator (fun t => ENNReal.ofReal (B * s / t)) t :=
          lintegral_add_left (measurable_const.indicator measurableSet_Ioc) _
      _ = ENNReal.ofReal (V * a) + ENNReal.ofReal (B * s * Real.log (T / a)) := by
          rw [lintegral_indicator measurableSet_Ioc, lintegral_indicator measurableSet_Ioc,
            setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul hV0,
            lintegral_Ioc_div ha0 haT (mul_nonneg hB hs.le)]
  calc ∫⁻ x, g x ∂ρ = ∫⁻ x, ENNReal.ofReal (f x) ∂ρ := lintegral_congr hgf
    _ = ∫⁻ t in Ioi 0, ρ {x | t < f x} :=
        lintegral_eq_lintegral_meas_lt ρ
          (Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg) hfm
    _ ≤ ∫⁻ t in Ioi (0 : ℝ),
        (Iio T).indicator (fun t => min (ENNReal.ofReal V) (ENNReal.ofReal (B * s / t))) t :=
        setLIntegral_mono' measurableSet_Ioi hdist
    _ ≤ ENNReal.ofReal (V * a) + ENNReal.ofReal (B * s * Real.log (T / a)) := h1D
    _ ≤ ENNReal.ofReal (s * (V + B * Real.posLog (T / s))) := by
        have hl0 : 0 ≤ Real.log (T / a) :=
          Real.log_nonneg ((one_le_div ha0).mpr haT)
        rw [← ENNReal.ofReal_add (mul_nonneg hV0 ha0.le) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have e1 : V * a ≤ V * s := mul_le_mul_of_nonneg_left has hV0
        have e2 : B * s * Real.log (T / a) ≤ B * s * Real.posLog (T / s) :=
          mul_le_mul_of_nonneg_left hlog (mul_nonneg hB hs.le)
        nlinarith

/-- **Logarithmic min-integral bound** for a weight `w`: for every `s > 0`,
`∫ min (T, s · w) dρ ≤ s · (B + D · log⁺ (1/s))`. This is the form in which a singular slice weight
enters the elementary template. It holds for weak-L¹ weights (`WeakL1.minLogBound`) and for
critically homogeneous weights on a pivot cone (`SLT.Template.minLogBound_pivotCone`). -/
def MinLogBound (ρ : Measure X) (w : X → ℝ≥0∞) (T B D : ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → ∫⁻ x, min (ENNReal.ofReal T) (ENNReal.ofReal s * w x) ∂ρ ≤
    ENNReal.ofReal (s * (B + D * Real.posLog s⁻¹))

/-- A weak-L¹ weight on a finite base satisfies the logarithmic min-integral bound. -/
theorem WeakL1.minLogBound {ρ : Measure X} {w : X → ℝ≥0∞} (hw : AEMeasurable w ρ)
    {B V T : ℝ} (hB : 0 ≤ B) (hV0 : 0 ≤ V) (hV : ρ univ ≤ ENNReal.ofReal V)
    (hBw : WeakL1 ρ w B) (hT : 0 < T) : MinLogBound ρ w T (V + B * Real.posLog T) B := by
  intro s hs
  refine (lintegral_min_le_of_weakL1 hw hB hV0 hV hBw hT hs).trans (ENNReal.ofReal_le_ofReal ?_)
  have h : Real.posLog (T / s) ≤ Real.posLog T + Real.posLog s⁻¹ := by
    rw [div_eq_mul_inv]; exact Real.posLog_mul
  have := mul_le_mul_of_nonneg_left h hB
  have := mul_le_mul_of_nonneg_left (add_le_add_left this V) hs.le
  linarith

/-- The logarithmic min-integral bound is invariant under measure-preserving embeddings. -/
theorem MinLogBound.comp_preimage {Y : Type*} [MeasurableSpace Y] {μ : Measure X}
    {ν : Measure Y} {f : X → Y} (hf : MeasurePreserving f μ ν) (hfe : MeasurableEmbedding f)
    {S : Set Y} {w : Y → ℝ≥0∞} {T B D : ℝ} (h : MinLogBound (ν.restrict S) w T B D) :
    MinLogBound (μ.restrict (f ⁻¹' S)) (w ∘ f) T B D := by
  intro s hs
  have e := hf.setLIntegral_comp_preimage_emb hfe
    (fun y => min (ENNReal.ofReal T) (ENNReal.ofReal s * w y)) S
  simp only [Function.comp_apply]
  rw [e]
  exact h s hs

end SLT.Template
