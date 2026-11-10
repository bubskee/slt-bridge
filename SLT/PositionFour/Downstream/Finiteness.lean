/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Downstream.LemmaOne
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Finiteness of the weighted unit sublevel volume

Section 3 of `complex_position_four.tex`: from the density interface (`DensityBound`,
`LocallyFiniteRow`) and Lemma 1,
`∫_{‖R(w)‖ < 1} (W_β(w₁) + W_β(w₂)) dw < ∞` for `0 ≤ β < 2` (`sublevel_weighted_lt_top`). At
`β = 0` this is the endpoint: the unit sublevel set of `R` has finite volume
(`volume_sublevel_lt_top`).

In row-cubic coordinates `R = (λ₁ - λ₂, y₁, y₂)`, so the sublevel set is
`{|λ₁ - λ₂| < 1, ‖y₁‖ < 1, ‖y₂‖ < 1}` (sup norms).

* the **compact part** `‖λ₁‖ ≤ 2` lies in `closedBall 0 2 × closedBall 0 3` and is finite by
  `LocallyFiniteRow` (the note uses local integrability of the density instead; the measures
  themselves suffice);
* the **far part** `‖λ₁‖ > 2` forces `‖λ₂‖ > 1`. By `DensityBound` it is bounded by
  `∬ 𝟙{|λ₁ - λ₂| < 1} g₁(λ₁) g₂(λ₂)`, with `gᵢ = m_{βᵢ} 𝟙{‖λ‖ > 1}`, and Hölder on the product
  space gives `≤ |B| ‖g₁‖_p ‖g₂‖_q` (no Young inequality is needed). The exponents are
  `p = 20/(10-β)` for the weighted row and `q = 20/(10+β)` for the unweighted one, which satisfy
  Lemma 1's conditions exactly when `β < 2`.
-/

@[expose] public section

namespace SLT.PositionFour.Downstream

open MeasureTheory Set Real Metric
open scoped ENNReal NNReal

/-! ### Splitting a cubic into `(λ, y)` -/

/-- `toCubic` is measurable as a function of `(λ, y)`. -/
theorem measurable_toCubic : Measurable fun w : (ℂ × ℂ) × (ℂ × ℂ) => toCubic w.1 w.2 := by
  refine measurable_pi_iff.mpr fun i => ?_
  fin_cases i
  exacts [measurable_fst.fst, measurable_fst.snd, measurable_snd.fst, measurable_snd.snd]

/-- The measurable equivalence `P ↦ ((P₀, P₁), (P₂, P₃))`. -/
noncomputable def cubicEquiv : Cubic ≃ᵐ (ℂ × ℂ) × (ℂ × ℂ) where
  toFun P := ((P 0, P 1), (P 2, P 3))
  invFun w := toCubic w.1 w.2
  left_inv P := by
    funext i; fin_cases i <;> rfl
  right_inv w := rfl
  measurable_toFun := by
    change Measurable fun P : Cubic => ((P 0, P 1), (P 2, P 3))
    fun_prop
  measurable_invFun := measurable_toCubic

/-- `cubicEquiv.symm = toCubic` preserves Lebesgue measure. -/
theorem measurePreserving_cubicEquiv_symm :
    MeasurePreserving cubicEquiv.symm volume volume := by
  refine ⟨cubicEquiv.symm.measurable, ?_⟩
  rw [MeasureTheory.volume_pi]
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [MeasurableEquiv.map_apply]
  have hpre : cubicEquiv.symm ⁻¹' univ.pi s = (s 0 ×ˢ s 1) ×ˢ (s 2 ×ˢ s 3) := by
    ext ⟨⟨a, b⟩, ⟨c, d⟩⟩
    simp only [mem_preimage, mem_univ_pi, mem_prod, Fin.forall_fin_succ, IsEmpty.forall_iff,
      and_true]
    simp [cubicEquiv, toCubic, and_assoc]
  rw [hpre, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod,
    Measure.prod_prod, Measure.prod_prod, Fin.prod_univ_four]
  ring

/-- Lebesgue integrals over cubics split as `∫ dλ ∫ dy`. -/
theorem lintegral_cubic {F : Cubic → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ P, F P = ∫⁻ lam : ℂ × ℂ, ∫⁻ y : ℂ × ℂ, F (toCubic lam y) := by
  rw [← measurePreserving_cubicEquiv_symm.lintegral_comp_emb
    cubicEquiv.symm.measurableEmbedding, Measure.volume_eq_prod,
    lintegral_prod (fun w => F (cubicEquiv.symm w))
      (hF.comp cubicEquiv.symm.measurable).aemeasurable]
  rfl

/-- The transverse marginal is measurable. -/
theorem measurable_transverseMarginal (β : ℝ) : Measurable (transverseMarginal β) :=
  ((measurable_densityBound β).comp measurable_toCubic).lintegral_prod_right'

/-! ### The sublevel set in row-cubic coordinates -/

/-- The leading map in row-cubic coordinates: `(P, Q) ↦ (P₀ - Q₀, P₁ - Q₁, P₂, P₃, Q₂, Q₃)`. -/
def cubicMap (PQ : Cubic × Cubic) : Fin 6 → ℂ :=
  ![PQ.1 0 - PQ.2 0, PQ.1 1 - PQ.2 1, PQ.1 2, PQ.1 3, PQ.2 2, PQ.2 3]

/-- `R = cubicMap ∘ (T × T)`. -/
theorem leadingMap_eq (w : Row × Row) :
    leadingMap w = cubicMap (rowCubic w.1, rowCubic w.2) := rfl

/-- The unit sublevel set of `R` in row-cubic coordinates. -/
def sublevelCubic : Set (Cubic × Cubic) := {PQ | ‖cubicMap PQ‖ < 1}

/-- `cubicMap` is continuous. -/
theorem continuous_cubicMap : Continuous cubicMap := by unfold cubicMap; fun_prop

/-- The sublevel set is measurable. -/
theorem measurableSet_sublevelCubic : MeasurableSet sublevelCubic :=
  measurableSet_lt (continuous_cubicMap.norm.measurable) measurable_const

/-- Membership in the sublevel set, coordinatewise. -/
theorem mem_sublevelCubic {P Q : Cubic} :
    (P, Q) ∈ sublevelCubic ↔ ‖P 0 - Q 0‖ < 1 ∧ ‖P 1 - Q 1‖ < 1 ∧ ‖P 2‖ < 1 ∧ ‖P 3‖ < 1 ∧
      ‖Q 2‖ < 1 ∧ ‖Q 3‖ < 1 := by
  simp only [sublevelCubic, mem_ofPred_eq, cubicMap]
  rw [pi_norm_lt_iff one_pos]
  simp [Fin.forall_fin_succ]

/-! ### Hölder near the diagonal -/

/-- Unit balls in `ℂ²` all have the same volume. -/
theorem volume_ball_prod_eq (x : ℂ × ℂ) : volume (ball x 1) = volume (ball (0 : ℂ × ℂ) 1) := by
  rw [show (0 : ℂ × ℂ) = ((0 : ℂ), (0 : ℂ)) from rfl, ← ball_prod_same, ← ball_prod_same,
    Measure.volume_eq_prod, Measure.prod_prod, Measure.prod_prod]
  simp only [Complex.volume_ball]

/-- **The near-diagonal Hölder bound** on `ℂ² × ℂ²`: for conjugate `p, q`,
`∬ 𝟙{|x - y| < 1} g₁(x) g₂(y) ≤ |B| ‖g₁‖_p ‖g₂‖_q`, so it is finite when both norms are. -/
theorem lintegral_near_diagonal_lt_top {p q : ℝ} (hpq : p.HolderConjugate q)
    {g₁ g₂ : ℂ × ℂ → ℝ≥0∞} (hg₁ : Measurable g₁) (hg₂ : Measurable g₂)
    (h₁ : ∫⁻ x, g₁ x ^ p < ∞) (h₂ : ∫⁻ x, g₂ x ^ q < ∞) :
    ∫⁻ z : (ℂ × ℂ) × (ℂ × ℂ), {z : (ℂ × ℂ) × (ℂ × ℂ) | ‖z.1 - z.2‖ < 1}.indicator
      (fun z => g₁ z.1 * g₂ z.2) z < ∞ := by
  set B := {z : (ℂ × ℂ) × (ℂ × ℂ) | ‖z.1 - z.2‖ < 1}
  have hB : MeasurableSet B := measurableSet_lt (by fun_prop) measurable_const
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  set F₁ := B.indicator fun z => g₁ z.1
  set F₂ := B.indicator fun z => g₂ z.2
  have hF₁ : Measurable F₁ := (hg₁.comp measurable_fst).indicator hB
  have hF₂ : Measurable F₂ := (hg₂.comp measurable_snd).indicator hB
  have hprod : (B.indicator fun z => g₁ z.1 * g₂ z.2) = F₁ * F₂ := by
    funext z
    by_cases hz : z ∈ B
    · simp [F₁, F₂, indicator_of_mem hz]
    · simp [F₁, F₂, indicator_of_notMem hz]
  have hball : volume (ball (0 : ℂ × ℂ) 1) < ∞ := measure_ball_lt_top
  -- the two `Lᵖ` norms
  have hpow : ∀ {r : ℝ}, 0 < r → ∀ (g : (ℂ × ℂ) × (ℂ × ℂ) → ℝ≥0∞) z,
      (B.indicator g z) ^ r = B.indicator (fun z => g z ^ r) z := by
    intro r hr g z
    by_cases hz : z ∈ B
    · simp [indicator_of_mem hz]
    · simp [indicator_of_notMem hz, ENNReal.zero_rpow_of_pos hr]
  have hI₁ : ∫⁻ z, F₁ z ^ p = volume (ball (0 : ℂ × ℂ) 1) * ∫⁻ x, g₁ x ^ p := by
    simp_rw [F₁, hpow hp0]
    have hm : Measurable fun z : (ℂ × ℂ) × (ℂ × ℂ) => B.indicator (fun z => g₁ z.1 ^ p) z :=
      ((hg₁.comp measurable_fst).pow_const p).indicator hB
    rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable,
      ← lintegral_const_mul _ (hg₁.pow_const p)]
    refine lintegral_congr fun x => ?_
    have e : (fun y => B.indicator (fun z => g₁ z.1 ^ p) (x, y)) =
        (ball x 1).indicator fun _ => g₁ x ^ p := by
      funext y; simp [B, indicator, mem_ball, dist_eq_norm, norm_sub_rev]
    rw [e, lintegral_indicator_const measurableSet_ball, volume_ball_prod_eq, mul_comm]
  have hI₂ : ∫⁻ z, F₂ z ^ q = volume (ball (0 : ℂ × ℂ) 1) * ∫⁻ y, g₂ y ^ q := by
    simp_rw [F₂, hpow hq0]
    have hm : Measurable fun z : (ℂ × ℂ) × (ℂ × ℂ) => B.indicator (fun z => g₂ z.2 ^ q) z :=
      ((hg₂.comp measurable_snd).pow_const q).indicator hB
    rw [Measure.volume_eq_prod, lintegral_prod_symm _ hm.aemeasurable,
      ← lintegral_const_mul _ (hg₂.pow_const q)]
    refine lintegral_congr fun y => ?_
    have e : (fun x => B.indicator (fun z => g₂ z.2 ^ q) (x, y)) =
        (ball y 1).indicator fun _ => g₂ y ^ q := by
      funext x; simp [B, indicator, mem_ball, dist_eq_norm]
    rw [e, lintegral_indicator_const measurableSet_ball, volume_ball_prod_eq, mul_comm]
  rw [hprod]
  refine lt_of_le_of_lt (ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq hF₁.aemeasurable
    hF₂.aemeasurable) (ENNReal.mul_lt_top ?_ ?_)
  · rw [hI₁]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (ENNReal.mul_lt_top hball h₁).ne
  · rw [hI₂]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (ENNReal.mul_lt_top hball h₂).ne

/-! ### The far part -/

/-- The marginal of a density over the transverse box, restricted to `‖λ‖ > 1`. -/
noncomputable def farMarginal (f : Cubic → ℝ≥0∞) (lam : ℂ × ℂ) : ℝ≥0∞ :=
  {lam : ℂ × ℂ | 1 < ‖lam‖}.indicator (fun lam => ∫⁻ y in ball (0 : ℂ × ℂ) 1,
    f (toCubic lam y)) lam

/-- `farMarginal` is measurable. -/
theorem measurable_farMarginal {f : Cubic → ℝ≥0∞} (hf : Measurable f) :
    Measurable (farMarginal f) :=
  (hf.comp measurable_toCubic).lintegral_prod_right'.indicator
    (measurableSet_lt measurable_const measurable_norm)

/-- `∫∫ G` over two cubics, in the coordinates `(λ₁, y₁, λ₂, y₂)`. -/
theorem lintegral_cubic_prod {G : Cubic × Cubic → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ z, G z ∂(volume.prod volume) =
      ∫⁻ l₁, ∫⁻ y₁, ∫⁻ l₂, ∫⁻ y₂, G (toCubic l₁ y₁, toCubic l₂ y₂) := by
  rw [lintegral_prod _ hG.aemeasurable, lintegral_cubic hG.lintegral_prod_right']
  refine lintegral_congr fun l₁ => lintegral_congr fun y₁ => ?_
  exact lintegral_cubic (hG.comp measurable_prodMk_left)

/-- The near-diagonal far region `{|λ₁ - λ₂| < 1, ‖λ₁‖ > 2}`. -/
def nearFar : Set ((ℂ × ℂ) × (ℂ × ℂ)) := {z | ‖z.1 - z.2‖ < 1 ∧ 2 < ‖z.1‖}

/-- **The far part of the sublevel set** for two density measures:
`(f₁ dP ⊗ f₂ dQ)(sublevel ∩ {‖λ₁‖ > 2}) ≤ ∬ 𝟙{|λ₁ - λ₂| < 1} g₁(λ₁) g₂(λ₂)`, with `gᵢ` the
transverse marginals restricted to `‖λ‖ > 1`. -/
theorem prod_withDensity_far_le {f₁ f₂ : Cubic → ℝ≥0∞} (hf₁ : Measurable f₁)
    (hf₂ : Measurable f₂) :
    ((volume.withDensity f₁).prod (volume.withDensity f₂))
        (sublevelCubic ∩ {PQ | 2 < ‖((PQ.1 0, PQ.1 1) : ℂ × ℂ)‖}) ≤
      ∫⁻ z : (ℂ × ℂ) × (ℂ × ℂ), {z : (ℂ × ℂ) × (ℂ × ℂ) | ‖z.1 - z.2‖ < 1}.indicator
        (fun z => farMarginal f₁ z.1 * farMarginal f₂ z.2) z := by
  set Far := sublevelCubic ∩ {PQ : Cubic × Cubic | 2 < ‖((PQ.1 0, PQ.1 1) : ℂ × ℂ)‖}
  have hFar : MeasurableSet Far :=
    measurableSet_sublevelCubic.inter (measurableSet_lt measurable_const (by fun_prop))
  have hD : MeasurableSet nearFar :=
    (measurableSet_lt (f := fun z : (ℂ × ℂ) × (ℂ × ℂ) => ‖z.1 - z.2‖) (g := fun _ => 1)
      (by fun_prop) measurable_const).inter
      (measurableSet_lt (f := fun _ => 2) (g := fun z : (ℂ × ℂ) × (ℂ × ℂ) => ‖z.1‖)
        measurable_const (by fun_prop))
  set m : (Cubic → ℝ≥0∞) → ℂ × ℂ → ℝ≥0∞ := fun f lam =>
    ∫⁻ y in ball (0 : ℂ × ℂ) 1, f (toCubic lam y)
  have hm : ∀ {f : Cubic → ℝ≥0∞}, Measurable f → Measurable (m f) := fun hf =>
    (hf.comp measurable_toCubic).lintegral_prod_right'
  set b : (Cubic → ℝ≥0∞) → ℂ × ℂ → ℂ × ℂ → ℝ≥0∞ := fun f lam =>
    (ball (0 : ℂ × ℂ) 1).indicator fun y => f (toCubic lam y)
  have hb : ∀ {f : Cubic → ℝ≥0∞}, Measurable f → Measurable fun w : (ℂ × ℂ) × (ℂ × ℂ) =>
      b f w.1 w.2 := by
    intro f hf
    have : Measurable fun w : (ℂ × ℂ) × (ℂ × ℂ) => (Prod.snd ⁻¹' ball (0 : ℂ × ℂ) 1).indicator
        (fun w : (ℂ × ℂ) × (ℂ × ℂ) => f (toCubic w.1 w.2)) w :=
      (hf.comp measurable_toCubic).indicator (measurableSet_ball.preimage measurable_snd)
    convert this using 2 with w
    rfl
  have hbm : ∀ (f : Cubic → ℝ≥0∞) lam, ∫⁻ y, b f lam y = m f lam := fun f lam =>
    lintegral_indicator measurableSet_ball _
  set Dind : (ℂ × ℂ) × (ℂ × ℂ) → ℝ≥0∞ := nearFar.indicator 1
  have hDm : Measurable Dind := measurable_one.indicator hD
  have hDl : ∀ l₁, Measurable fun l₂ => Dind (l₁, l₂) * m f₂ l₂ := fun l₁ =>
    (hDm.comp (measurable_const.prodMk measurable_id)).mul (hm hf₂)
  have hbl : ∀ {f : Cubic → ℝ≥0∞}, Measurable f → ∀ l, Measurable fun y => b f l y :=
    fun hf l => (hb hf).comp (measurable_const.prodMk measurable_id)
  -- the pointwise bound
  have hpt : ∀ l₁ y₁ l₂ y₂, Far.indicator (fun z => f₁ z.1 * f₂ z.2)
      (toCubic l₁ y₁, toCubic l₂ y₂) ≤ Dind (l₁, l₂) * (b f₁ l₁ y₁ * b f₂ l₂ y₂) := by
    intro l₁ y₁ l₂ y₂
    by_cases h : (toCubic l₁ y₁, toCubic l₂ y₂) ∈ Far
    · obtain ⟨hs, hfar⟩ := h
      rw [mem_sublevelCubic] at hs
      obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hs
      have hl : ‖l₁ - l₂‖ < 1 := by
        rw [Prod.norm_def]; exact max_lt h0 h1
      have hy₁ : y₁ ∈ ball (0 : ℂ × ℂ) 1 := by
        rw [mem_ball_zero_iff, Prod.norm_def]; exact max_lt h2 h3
      have hy₂ : y₂ ∈ ball (0 : ℂ × ℂ) 1 := by
        rw [mem_ball_zero_iff, Prod.norm_def]; exact max_lt h4 h5
      have hD' : (l₁, l₂) ∈ nearFar := ⟨hl, hfar⟩
      simp only [Dind, b, indicator_of_mem hD', indicator_of_mem hy₁, indicator_of_mem hy₂,
        Pi.one_apply, one_mul, indicator_of_mem (show (toCubic l₁ y₁, toCubic l₂ y₂) ∈ Far
          from ⟨(mem_sublevelCubic).mpr ⟨h0, h1, h2, h3, h4, h5⟩, hfar⟩)]
      exact le_rfl
    · rw [indicator_of_notMem h]; exact bot_le
  rw [prod_withDensity hf₁ hf₂, withDensity_apply _ hFar, ← lintegral_indicator hFar,
    lintegral_cubic_prod (G := Far.indicator fun z => f₁ z.1 * f₂ z.2)
      (((hf₁.comp measurable_fst).mul (hf₂.comp measurable_snd)).indicator hFar)]
  calc ∫⁻ l₁, ∫⁻ y₁, ∫⁻ l₂, ∫⁻ y₂, Far.indicator (fun z => f₁ z.1 * f₂ z.2)
          (toCubic l₁ y₁, toCubic l₂ y₂)
      ≤ ∫⁻ l₁, ∫⁻ y₁, ∫⁻ l₂, ∫⁻ y₂, Dind (l₁, l₂) * (b f₁ l₁ y₁ * b f₂ l₂ y₂) :=
        lintegral_mono fun l₁ => lintegral_mono fun y₁ => lintegral_mono fun l₂ =>
          lintegral_mono fun y₂ => hpt l₁ y₁ l₂ y₂
    _ = ∫⁻ l₁, m f₁ l₁ * ∫⁻ l₂, Dind (l₁, l₂) * m f₂ l₂ := by
        refine lintegral_congr fun l₁ => ?_
        have inner : ∀ y₁, ∫⁻ l₂, ∫⁻ y₂, Dind (l₁, l₂) * (b f₁ l₁ y₁ * b f₂ l₂ y₂) =
            b f₁ l₁ y₁ * ∫⁻ l₂, Dind (l₁, l₂) * m f₂ l₂ := by
          intro y₁
          rw [← lintegral_const_mul _ (hDl l₁)]
          refine lintegral_congr fun l₂ => ?_
          have h' : Measurable fun y => Dind (l₁, l₂) * b f₂ l₂ y := (hbl hf₂ l₂).const_mul _
          rw [← hbm, ← lintegral_const_mul _ (hbl hf₂ l₂), ← lintegral_const_mul _ h']
          refine lintegral_congr fun y₂ => ?_
          ring
        simp_rw [inner]
        rw [lintegral_mul_const _ (hbl hf₁ l₁), hbm]
    _ = ∫⁻ l₁, ∫⁻ l₂, m f₁ l₁ * (Dind (l₁, l₂) * m f₂ l₂) := by
        refine lintegral_congr fun l₁ => ?_
        rw [lintegral_const_mul _ (hDl l₁)]
    _ ≤ ∫⁻ l₁, ∫⁻ l₂, {z : (ℂ × ℂ) × (ℂ × ℂ) | ‖z.1 - z.2‖ < 1}.indicator
          (fun z => farMarginal f₁ z.1 * farMarginal f₂ z.2) (l₁, l₂) := by
        refine lintegral_mono fun l₁ => lintegral_mono fun l₂ => ?_
        by_cases h : (l₁, l₂) ∈ nearFar
        · obtain ⟨h1, h2⟩ := h
          have hl₁ : 1 < ‖l₁‖ := by linarith
          have hl₂ : 1 < ‖l₂‖ := by
            have := norm_sub_norm_le l₁ l₂
            linarith
          simp only [Dind, indicator_of_mem (show (l₁, l₂) ∈ nearFar from ⟨h1, h2⟩),
            Pi.one_apply, one_mul,
            indicator_of_mem (show (l₁, l₂) ∈ {z : (ℂ × ℂ) × (ℂ × ℂ) | ‖z.1 - z.2‖ < 1} from h1),
            farMarginal, indicator_of_mem (show l₁ ∈ {lam : ℂ × ℂ | 1 < ‖lam‖} from hl₁),
            indicator_of_mem (show l₂ ∈ {lam : ℂ × ℂ | 1 < ‖lam‖} from hl₂)]
          exact le_rfl
        · simp only [Dind, indicator_of_notMem h, mul_zero, zero_mul]; exact bot_le
    _ = _ := by
        have hB : MeasurableSet {z : (ℂ × ℂ) × (ℂ × ℂ) | ‖z.1 - z.2‖ < 1} :=
          measurableSet_lt (f := fun z : (ℂ × ℂ) × (ℂ × ℂ) => ‖z.1 - z.2‖) (g := fun _ => 1)
            (by fun_prop) measurable_const
        have hmF : Measurable fun z : (ℂ × ℂ) × (ℂ × ℂ) =>
            {z : (ℂ × ℂ) × (ℂ × ℂ) | ‖z.1 - z.2‖ < 1}.indicator
              (fun z => farMarginal f₁ z.1 * farMarginal f₂ z.2) z :=
          (((measurable_farMarginal hf₁).comp measurable_fst).mul
            ((measurable_farMarginal hf₂).comp measurable_snd)).indicator hB
        rw [Measure.volume_eq_prod (ℂ × ℂ) (ℂ × ℂ), lintegral_prod _ hmF.aemeasurable]

/-! ### Assembly -/

/-- The row measures are s-finite (they are pushforwards of s-finite measures). -/
instance sFinite_rowMeasure (β : ℝ) : SFinite (rowMeasure β) := by
  unfold rowMeasure; infer_instance

/-- Product measures are monotone in each factor. -/
theorem prod_apply_mono {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ μ' : Measure α} {ν ν' : Measure β} [SFinite ν] [SFinite ν'] (hμ : μ ≤ μ') (hν : ν ≤ ν')
    {s : Set (α × β)} (hs : MeasurableSet s) : (μ.prod ν) s ≤ (μ'.prod ν') s := by
  rw [Measure.prod_apply hs, Measure.prod_apply hs]
  exact lintegral_mono' hμ fun x => Measure.le_iff'.mp hν _

/-- The `Lᵖ` norm of `farMarginal (densityBound β)` is Lemma 1's integral. -/
theorem lintegral_farMarginal_rpow (β : ℝ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, farMarginal (densityBound β) x ^ p =
      ∫⁻ lam in {lam : ℂ × ℂ | 1 < ‖lam‖}, transverseMarginal β lam ^ p := by
  rw [← lintegral_indicator (measurableSet_lt measurable_const measurable_norm)]
  refine lintegral_congr fun lam => ?_
  by_cases h : lam ∈ {lam : ℂ × ℂ | 1 < ‖lam‖}
  · simp only [farMarginal, indicator_of_mem h]; rfl
  · simp only [farMarginal, indicator_of_notMem h, ENNReal.zero_rpow_of_pos hp]

/-- **The product of two row measures charges the sublevel set finitely**, given the density
interface for both rows and Lemma 1's `Lᵖ` and `L^q` bounds with conjugate `p, q`. -/
theorem prod_rowMeasure_sublevel_lt_top {β₁ β₂ C₁ C₂ p q : ℝ} (hpq : p.HolderConjugate q)
    (hD₁ : DensityBound β₁ C₁) (hD₂ : DensityBound β₂ C₂)
    (hL₁ : LocallyFiniteRow β₁) (hL₂ : LocallyFiniteRow β₂)
    (h₁ : ∫⁻ lam in {lam : ℂ × ℂ | 1 < ‖lam‖}, transverseMarginal β₁ lam ^ p < ∞)
    (h₂ : ∫⁻ lam in {lam : ℂ × ℂ | 1 < ‖lam‖}, transverseMarginal β₂ lam ^ q < ∞) :
    ((rowMeasure β₁).prod (rowMeasure β₂)) sublevelCubic < ∞ := by
  set Far := sublevelCubic ∩ {PQ : Cubic × Cubic | 2 < ‖((PQ.1 0, PQ.1 1) : ℂ × ℂ)‖}
  have hFar : MeasurableSet Far :=
    measurableSet_sublevelCubic.inter (measurableSet_lt measurable_const (by fun_prop))
  have hsub : sublevelCubic ⊆ closedBall 0 2 ×ˢ closedBall 0 3 ∪ Far := by
    rintro ⟨P, Q⟩ h
    by_cases hl : 2 < ‖((P 0, P 1) : ℂ × ℂ)‖
    · exact Or.inr ⟨h, hl⟩
    · left
      obtain ⟨h0, h1, h2, h3, h4, h5⟩ := mem_sublevelCubic.mp h
      rw [not_lt, Prod.norm_def, max_le_iff] at hl
      obtain ⟨hl0, hl1⟩ := hl
      have hq0 : ‖Q 0‖ ≤ 3 := by
        have := norm_sub_norm_le (P 0) (Q 0); have := norm_sub_rev (P 0) (Q 0)
        have := norm_le_insert' (Q 0) (P 0); linarith
      have hq1 : ‖Q 1‖ ≤ 3 := by
        have := norm_le_insert' (Q 1) (P 1); rw [norm_sub_rev] at this; linarith
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall_zero_iff]
        refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_
        fin_cases i
        exacts [hl0, hl1, by simp only [Fin.reduceFinMk]; linarith,
          by simp only [Fin.reduceFinMk]; linarith]
      · rw [mem_closedBall_zero_iff]
        refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_
        fin_cases i
        exacts [hq0, hq1, by simp only [Fin.reduceFinMk]; linarith,
          by simp only [Fin.reduceFinMk]; linarith]
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  refine lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt (measure_union_le _ _)
    (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩))
  · rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top (hL₁ 2) (hL₂ 3)
  · set ν₁ := (volume : Measure Cubic).withDensity (densityBound β₁)
    set ν₂ := (volume : Measure Cubic).withDensity (densityBound β₂)
    calc ((rowMeasure β₁).prod (rowMeasure β₂)) Far
        ≤ ((ENNReal.ofReal C₁ • ν₁).prod (ENNReal.ofReal C₂ • ν₂)) Far :=
          prod_apply_mono hD₁ hD₂ hFar
      _ = ENNReal.ofReal C₁ * (ENNReal.ofReal C₂ * (ν₁.prod ν₂) Far) := by
          rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.smul_apply,
            Measure.smul_apply, smul_eq_mul, smul_eq_mul]
      _ ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal C₂ *
            ∫⁻ z : (ℂ × ℂ) × (ℂ × ℂ), {z : (ℂ × ℂ) × (ℂ × ℂ) | ‖z.1 - z.2‖ < 1}.indicator
              (fun z => farMarginal (densityBound β₁) z.1 * farMarginal (densityBound β₂) z.2)
              z) := by
          gcongr
          exact prod_withDensity_far_le (measurable_densityBound β₁) (measurable_densityBound β₂)
      _ < ∞ := by
          refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top
            ENNReal.ofReal_lt_top (lintegral_near_diagonal_lt_top hpq
              (measurable_farMarginal (measurable_densityBound β₁))
              (measurable_farMarginal (measurable_densityBound β₂)) ?_ ?_))
          · rwa [lintegral_farMarginal_rpow β₁ hp0]
          · rwa [lintegral_farMarginal_rpow β₂ hq0]

/-- `T` is measurable. -/
theorem measurable_rowCubic : Measurable rowCubic := by
  have : Continuous rowCubic := by unfold rowCubic cube; fun_prop
  exact this.measurable

/-- `W_β` is measurable. -/
theorem measurable_rowWeight (β : ℝ) : Measurable (rowWeight β) := by
  unfold rowWeight; fun_prop

/-- `W_β ≥ 0`. -/
theorem rowWeight_nonneg (β : ℝ) (r : Row) : 0 ≤ rowWeight β r :=
  Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _

/-- `W₀ = 3`. -/
theorem rowWeight_zero (r : Row) : rowWeight 0 r = 3 := by
  simp [rowWeight]

/-- A product weight on the preimage of a cubic set is the product row measure of that set. -/
theorem setLIntegral_preimage_eq_prod (β₁ β₂ : ℝ) {s : Set (Cubic × Cubic)}
    (hs : MeasurableSet s) :
    ∫⁻ w in Prod.map rowCubic rowCubic ⁻¹' s,
        ENNReal.ofReal (rowWeight β₁ w.1) * ENNReal.ofReal (rowWeight β₂ w.2) =
      ((rowMeasure β₁).prod (rowMeasure β₂)) s := by
  have hT := measurable_rowCubic
  rw [rowMeasure, rowMeasure, Measure.map_prod_map _ _ hT hT,
    Measure.map_apply (hT.prodMap hT) hs,
    prod_withDensity (measurable_rowWeight β₁).ennreal_ofReal
      (measurable_rowWeight β₂).ennreal_ofReal,
    withDensity_apply _ (hs.preimage (hT.prodMap hT)), Measure.volume_eq_prod]

/-- **Finiteness of the weighted unit sublevel volume** (`complex_position_four.tex`, Section 3).
From the density interface for the weights `0` and `β`, with `0 ≤ β < 2`:
`∫_{‖R(w)‖ < 1} (W_β(w₁) + W_β(w₂)) dw < ∞`. -/
theorem sublevel_weighted_lt_top {β C₀ C : ℝ} (hβ0 : 0 ≤ β) (hβ2 : β < 2)
    (hD₀ : DensityBound 0 C₀) (hDβ : DensityBound β C)
    (hL₀ : LocallyFiniteRow 0) (hLβ : LocallyFiniteRow β) :
    ∫⁻ w in {w : Row × Row | ‖leadingMap w‖ < 1},
      ENNReal.ofReal (rowWeight β w.1 + rowWeight β w.2) < ∞ := by
  set S := {w : Row × Row | ‖leadingMap w‖ < 1}
  have hS : S = Prod.map rowCubic rowCubic ⁻¹' sublevelCubic := rfl
  have hSm : MeasurableSet S := by
    rw [hS]; exact measurableSet_sublevelCubic.preimage
      (measurable_rowCubic.prodMap measurable_rowCubic)
  -- the Hölder pair
  set p := 20 / (10 - β) with hp
  set q := 20 / (10 + β) with hq
  have hpq : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff, hp, hq, inv_div, inv_div]
    refine ⟨?_, by field_simp; ring⟩
    rw [lt_div_iff₀ (by linarith)]; linarith
  have hpL : 10 / (6 - β) < p := by
    rw [hp, div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have hqL : 10 / (6 - 0) < q := by
    rw [hq, div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have hβp := lemma_one hβ0 hβ2 hpL
  have h0q := lemma_one le_rfl (by norm_num) hqL
  have hpq' : q.HolderConjugate p := hpq.symm
  have hβq : 10 / (6 - 0) < q := hqL
  have hp' : 10 / (6 - β) < p := hpL
  have T₁ := prod_rowMeasure_sublevel_lt_top hpq hDβ hD₀ hLβ hL₀ hβp h0q
  have T₂ := prod_rowMeasure_sublevel_lt_top hpq' hD₀ hDβ hL₀ hLβ h0q hβp
  -- split the weight and compare with the product measures
  have hW : ∀ w : Row × Row, ENNReal.ofReal (rowWeight β w.1 + rowWeight β w.2) =
      ENNReal.ofReal (rowWeight β w.1) + ENNReal.ofReal (rowWeight β w.2) := fun w =>
    ENNReal.ofReal_add (rowWeight_nonneg _ _) (rowWeight_nonneg _ _)
  simp_rw [hW]
  have hm1 : Measurable fun w : Row × Row => ENNReal.ofReal (rowWeight β w.1) :=
    (measurable_rowWeight β).ennreal_ofReal.comp measurable_fst
  rw [lintegral_add_left hm1]
  have h3 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (rowWeight 0 (0 : Row)) := by
    rw [rowWeight_zero]; norm_num
  refine ENNReal.add_lt_top.mpr ⟨lt_of_le_of_lt ?_ T₁, lt_of_le_of_lt ?_ T₂⟩
  · rw [← setLIntegral_preimage_eq_prod β 0 measurableSet_sublevelCubic, ← hS]
    refine lintegral_mono fun w => ?_
    rw [rowWeight_zero, ← rowWeight_zero (0 : Row)]
    exact le_mul_of_one_le_right bot_le h3
  · rw [← setLIntegral_preimage_eq_prod 0 β measurableSet_sublevelCubic, ← hS]
    refine lintegral_mono fun w => ?_
    rw [rowWeight_zero, ← rowWeight_zero (0 : Row)]
    exact le_mul_of_one_le_left bot_le h3

/-- **The endpoint**: the unit sublevel set of the leading map `R` has finite volume. -/
theorem volume_sublevel_lt_top {C₀ : ℝ} (hD₀ : DensityBound 0 C₀) (hL₀ : LocallyFiniteRow 0) :
    volume {w : Row × Row | ‖leadingMap w‖ < 1} < ∞ := by
  have h := sublevel_weighted_lt_top le_rfl (by norm_num) hD₀ hD₀ hL₀ hL₀
  simp_rw [rowWeight_zero] at h
  rw [setLIntegral_const] at h
  refine (ENNReal.mul_lt_top_iff.mp h).elim (fun h' => h'.2) fun h' => h'.elim
    (fun h'' => absurd h'' (by norm_num)) fun h'' => h''.symm ▸ ENNReal.zero_lt_top

end SLT.PositionFour.Downstream
