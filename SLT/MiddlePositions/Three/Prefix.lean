/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Three.Marginal

/-!
# The uniform translated prefix bound at position three

The note's Lemma "Uniform translated prefix bound" (Section 5 of `complex_middle_positions.tex`).

* `lintegral_kernel_le`: on a finite-dimensional real normed space with an additive Haar measure,
  if `m ≤ f + g` with `f ∈ L¹` and `g ∈ L²`, then for every translation `z`,
  `∬ 𝟙{‖x - y - z‖ < 1} m(x) m(y) ≤ B(‖f‖₁, ‖g‖₂², |B₁|)`, a bound independent of `z`.
  The note bounds the mixed terms by Cauchy–Schwarz; here every term is bounded by the
  elementary `a ≤ 1 + a²` and `ab ≤ a² + b²`, which give the same finiteness. The lemma is used
  twice: for the prefix marginal on `ℂ²` (this file) and for the suffix kernel on `ℂ` (assembly).
* `lintegral_W2_twoCube_le`: `WeightedTwoCubeBound` in integral form.
* `lintegral_marginal_mul`: `∫ F(P) 𝟙{|P₂|,|P₃| < 1} ψ(P₀, P₁) dP = ∫ m(λ) ψ(λ) dλ`.
* `prefix_bound`: the `W₂ ⊗ W₂`-weighted mass of the position-three prefix constraints
  `|p^k_2|, |p^k_3| < 1`, `|p¹₁ - p²₁| < 1`, `|p¹₀ - p²₀ + c| < 1` is bounded uniformly in `c`.
-/

@[expose] public section

namespace SLT.MiddlePositions.Three

open MeasureTheory Set Real Metric SLT.PositionFour SLT.PositionFour.Downstream
open scoped ENNReal NNReal

/-! ### Two elementary inequalities in `ℝ≥0∞` -/

/-- `a ≤ 1 + a²`. -/
theorem le_one_add_sq (a : ℝ≥0∞) : a ≤ 1 + a ^ 2 := by
  rcases le_total a 1 with h | h
  · exact h.trans le_self_add
  · calc a = a * 1 := (mul_one a).symm
      _ ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ 1 + a ^ 2 := le_add_self

/-! ### The translated kernel bound -/

/-- The translated unit kernel `𝟙{‖x - y - z‖ < 1}`, as a function of `y`. -/
theorem indicator_ball_sub_left {E : Type*} [NormedAddCommGroup E] (x y z : E) :
    (ball z 1).indicator (1 : E → ℝ≥0∞) (x - y) = (ball (x - z) 1).indicator 1 y := by
  have h : x - y ∈ ball z 1 ↔ y ∈ ball (x - z) 1 := by
    simp only [mem_ball, dist_eq_norm]
    rw [← norm_neg]; congr! 2; abel
  by_cases hx : x - y ∈ ball z 1
  · rw [indicator_of_mem hx, indicator_of_mem (h.mp hx)]; rfl
  · rw [indicator_of_notMem hx, indicator_of_notMem (mt h.mpr hx)]

/-- The translated unit kernel `𝟙{‖x - y - z‖ < 1}`, as a function of `x`. -/
theorem indicator_ball_sub_right {E : Type*} [NormedAddCommGroup E] (x y z : E) :
    (ball z 1).indicator (1 : E → ℝ≥0∞) (x - y) = (ball (y + z) 1).indicator 1 x := by
  have h : x - y ∈ ball z 1 ↔ x ∈ ball (y + z) 1 := by
    simp only [mem_ball, dist_eq_norm, sub_sub]
  by_cases hx : x - y ∈ ball z 1
  · rw [indicator_of_mem hx, indicator_of_mem (h.mp hx)]; rfl
  · rw [indicator_of_notMem hx, indicator_of_notMem (mt h.mpr hx)]

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **The uniform translated kernel bound.** If `m ≤ f + g` with `∫ f < ∞` and `∫ g² < ∞`, then
for every `z`, `∬ 𝟙{‖x - y - z‖ < 1} m(x) m(y) ≤ ‖f‖₁(‖f‖₁ + V + ‖g‖₂²) + ‖g‖₂²(‖f‖₁ + V) +
V(‖f‖₁ + ‖g‖₂²)`, where `V` is the volume of the unit ball. -/
theorem lintegral_kernel_le {m f g : E → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hmfg : ∀ x, m x ≤ f x + g x) (z : E) :
    ∫⁻ x, ∫⁻ y, (ball z 1).indicator 1 (x - y) * (m x * m y) ∂μ ∂μ ≤
      (∫⁻ x, f x ∂μ) * ((∫⁻ x, f x ∂μ) + μ (ball 0 1) + ∫⁻ x, g x ^ 2 ∂μ) +
        (∫⁻ x, g x ^ 2 ∂μ) * ((∫⁻ x, f x ∂μ) + μ (ball 0 1)) +
        μ (ball 0 1) * ((∫⁻ x, f x ∂μ) + ∫⁻ x, g x ^ 2 ∂μ) := by
  set k : E → E → ℝ≥0∞ := fun x y => (ball z 1).indicator 1 (x - y) with hk
  set If := ∫⁻ x, f x ∂μ
  set Ig := ∫⁻ x, g x ^ 2 ∂μ
  set V := μ (ball (0 : E) 1)
  have hkm : Measurable fun p : E × E => k p.1 p.2 :=
    (measurable_one.indicator measurableSet_ball).comp (measurable_fst.sub measurable_snd)
  have hk1 : ∀ x, ∫⁻ y, k x y ∂μ = V := fun x => by
    simp only [hk, indicator_ball_sub_left]
    rw [lintegral_indicator_one measurableSet_ball, Measure.addHaar_ball_center]
  have hk2 : ∀ y, ∫⁻ x, k x y ∂μ = V := fun y => by
    simp only [hk, indicator_ball_sub_right]
    rw [lintegral_indicator_one measurableSet_ball, Measure.addHaar_ball_center]
  have hg2 : Measurable fun x => g x ^ 2 := hg.pow_const 2
  -- the pointwise bound
  have hpt : ∀ x y, k x y * (m x * m y) ≤
      (f x * (f y + k x y + g y ^ 2) + g x ^ 2 * (f y + k x y)) + k x y * (f y + g y ^ 2) := by
    intro x y
    by_cases hxy : x - y ∈ ball z 1
    · have h1 : k x y = 1 := by simp only [hk, indicator_of_mem hxy, Pi.one_apply]
      rw [h1, one_mul]
      calc m x * m y ≤ (f x + g x) * (f y + g y) := mul_le_mul' (hmfg x) (hmfg y)
        _ = f x * f y + f x * g y + g x * f y + g x * g y := by ring
        _ ≤ f x * f y + f x * (1 + g y ^ 2) + f y * (1 + g x ^ 2) + (g x ^ 2 + g y ^ 2) := by
            have e1 : f x * g y ≤ f x * (1 + g y ^ 2) := by gcongr; exact le_one_add_sq _
            have e2 : g x * f y ≤ f y * (1 + g x ^ 2) := by
              rw [mul_comm]; gcongr; exact le_one_add_sq _
            have e3 := Pushforward.mul_le_sq_add_sq (g x) (g y)
            exact add_le_add (add_le_add (add_le_add le_rfl e1) e2) e3
        _ = _ := by ring
    · have h0 : k x y = 0 := by simp only [hk, indicator_of_notMem hxy]
      rw [h0, zero_mul]; exact bot_le
  -- the inner integral of the first group
  have hA : ∀ x, ∫⁻ y, (f x * (f y + k x y + g y ^ 2) + g x ^ 2 * (f y + k x y)) ∂μ =
      f x * (If + V + Ig) + g x ^ 2 * (If + V) := by
    intro x
    have hkx : Measurable (k x) := hkm.comp (measurable_const.prodMk measurable_id)
    have m1 : Measurable fun y => f y + k x y := by fun_prop
    have m2 : Measurable fun y => f y + k x y + g y ^ 2 := by fun_prop
    have m3 : Measurable fun y => f x * (f y + k x y + g y ^ 2) := by fun_prop
    rw [lintegral_add_left m3, lintegral_const_mul _ m2, lintegral_const_mul _ m1,
      lintegral_add_left m1, lintegral_add_left hf, hk1]
  have hB : ∫⁻ x, ∫⁻ y, k x y * (f y + g y ^ 2) ∂μ ∂μ = V * (If + Ig) := by
    have hfg : Measurable fun y => f y + g y ^ 2 := by fun_prop
    rw [lintegral_lintegral_swap ((hkm.mul (hfg.comp measurable_snd)).aemeasurable)]
    have e : ∀ y, ∫⁻ x, k x y * (f y + g y ^ 2) ∂μ = V * (f y + g y ^ 2) := fun y => by
      have hky : Measurable fun x => k x y := hkm.comp (measurable_id.prodMk measurable_const)
      rw [lintegral_mul_const _ hky, hk2]
    rw [lintegral_congr e, lintegral_const_mul _ hfg, lintegral_add_left hf]
  have hmA : ∀ x, Measurable fun y => f x * (f y + k x y + g y ^ 2) + g x ^ 2 * (f y + k x y) :=
    fun x => by
      have hkx : Measurable (k x) := hkm.comp (measurable_const.prodMk measurable_id)
      fun_prop
  calc ∫⁻ x, ∫⁻ y, k x y * (m x * m y) ∂μ ∂μ
      ≤ ∫⁻ x, ∫⁻ y, ((f x * (f y + k x y + g y ^ 2) + g x ^ 2 * (f y + k x y)) +
          k x y * (f y + g y ^ 2)) ∂μ ∂μ := lintegral_mono fun x => lintegral_mono (hpt x)
    _ = ∫⁻ x, ((f x * (If + V + Ig) + g x ^ 2 * (If + V)) +
          ∫⁻ y, k x y * (f y + g y ^ 2) ∂μ) ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_add_left (hmA x), hA]
    _ = (If * (If + V + Ig) + Ig * (If + V)) + V * (If + Ig) := by
        have n1 : Measurable fun x => f x * (If + V + Ig) := by fun_prop
        have n2 : Measurable fun x => f x * (If + V + Ig) + g x ^ 2 * (If + V) := by fun_prop
        rw [lintegral_add_left n2, hB, lintegral_add_left n1, lintegral_mul_const _ hf,
          lintegral_mul_const _ hg2]

omit [BorelSpace E] in
/-- The bound of `lintegral_kernel_le` is finite once `‖f‖₁` and `‖g‖₂²` are. -/
theorem kernel_bound_lt_top {If Ig : ℝ≥0∞} (hf : If < ∞) (hg : Ig < ∞) :
    If * (If + μ (ball 0 1) + Ig) + Ig * (If + μ (ball 0 1)) + μ (ball 0 1) * (If + Ig) < ∞ := by
  have hV : μ (ball (0 : E) 1) < ∞ := measure_ball_lt_top
  finiteness

end Kernel

/-- `(s.indicator m)² = s.indicator m²`, integrated. -/
theorem lintegral_indicator_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (m : α → ℝ≥0∞) :
    ∫⁻ x, s.indicator m x ^ 2 ∂μ = ∫⁻ x in s, m x ^ 2 ∂μ := by
  rw [← lintegral_indicator hs]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ s
  · simp [indicator_of_mem hx]
  · simp [indicator_of_notMem hx]

/-! ### The weighted two-cube bound in integral form -/

/-- `twoCube` is measurable. -/
theorem measurable_twoCube : Measurable twoCube := by unfold twoCube cube; fun_prop

/-- `W₂` is measurable. -/
theorem measurable_W2 : Measurable W2 := by unfold W2; fun_prop

/-- **`WeightedTwoCubeBound` in integral form**: for measurable `φ ≥ 0` on cubic space,
`∫ W₂(g) φ(Ψ(g)) dg ≤ C ∫ F(P) φ(P) dP`. -/
theorem lintegral_W2_twoCube_le {C : ℝ} (hW : WeightedTwoCubeBound C) {φ : Cubic → ℝ≥0∞}
    (hφ : Measurable φ) :
    ∫⁻ g : Form × Form, ENNReal.ofReal (W2 g) * φ (twoCube g) ≤
      ENNReal.ofReal C * ∫⁻ P, F P * φ P := by
  have hw : Measurable fun g : Form × Form => ENNReal.ofReal (W2 g) := measurable_W2.ennreal_ofReal
  calc ∫⁻ g : Form × Form, ENNReal.ofReal (W2 g) * φ (twoCube g)
      = ∫⁻ g, φ (twoCube g) ∂(volume.withDensity fun g => ENNReal.ofReal (W2 g)) :=
        (lintegral_withDensity_eq_lintegral_mul _ hw (hφ.comp measurable_twoCube)).symm
    _ = ∫⁻ P, φ P ∂((volume.withDensity fun g => ENNReal.ofReal (W2 g)).map twoCube) :=
        (lintegral_map hφ measurable_twoCube).symm
    _ ≤ ∫⁻ P, φ P ∂(ENNReal.ofReal C • (volume : Measure Cubic).withDensity F) :=
        lintegral_mono' hW le_rfl
    _ = ENNReal.ofReal C * ∫⁻ P, F P * φ P := by
        rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ measurable_F hφ]
        rfl

/-! ### From cubic space to the marginal -/

/-- The box indicator `𝟙{|P₂|, |P₃| < 1}`. -/
noncomputable def boxInd (P : Cubic) : ℝ≥0∞ := (ball (0 : ℂ × ℂ) 1).indicator 1 (P 2, P 3)

/-- The box indicator is measurable. -/
theorem measurable_boxInd : Measurable boxInd :=
  (measurable_one.indicator measurableSet_ball).comp (by fun_prop)

/-- The coordinates `λ = (P₀, P₁)`. -/
def lamOf (P : Cubic) : ℂ × ℂ := (P 0, P 1)

/-- `lamOf` is measurable. -/
theorem measurable_lamOf : Measurable lamOf := by unfold lamOf; fun_prop

/-- **Integrating out the box**: `∫ F(P) 𝟙_box(P) ψ(λ(P)) dP = ∫ m(λ) ψ(λ) dλ`. -/
theorem lintegral_marginal_mul {ψ : ℂ × ℂ → ℝ≥0∞} (hψ : Measurable ψ) :
    ∫⁻ P, F P * boxInd P * ψ (lamOf P) = ∫⁻ lam, marginal lam * ψ lam := by
  have hm : Measurable fun P : Cubic => F P * boxInd P * ψ (lamOf P) :=
    (measurable_F.mul measurable_boxInd).mul (hψ.comp measurable_lamOf)
  rw [lintegral_cubic hm]
  refine lintegral_congr fun lam => ?_
  have e : ∀ y : ℂ × ℂ, F (toCubic lam y) * boxInd (toCubic lam y) * ψ (lamOf (toCubic lam y)) =
      (ball (0 : ℂ × ℂ) 1).indicator (fun y => F (toCubic lam y)) y * ψ lam := by
    intro y
    have h1 : lamOf (toCubic lam y) = lam := rfl
    have h2 : ((toCubic lam y) 2, (toCubic lam y) 3) = y := rfl
    rw [h1, boxInd, h2]
    by_cases hy : y ∈ ball (0 : ℂ × ℂ) 1
    · simp [indicator_of_mem hy]
    · simp [indicator_of_notMem hy]
  have hF' : Measurable fun y : ℂ × ℂ => F (toCubic lam y) :=
    measurable_F.comp (measurable_toCubic.comp (measurable_const.prodMk measurable_id))
  rw [lintegral_congr e, lintegral_mul_const _ (hF'.indicator measurableSet_ball),
    lintegral_indicator measurableSet_ball, marginal]

/-! ### The prefix bound -/

/-- The position-three prefix constraints on a pair of prefix cubics, with translation `c`:
`|P¹₂|, |P¹₃|, |P²₂|, |P²₃| < 1` and `max(|P¹₀ - P²₀ + c|, |P¹₁ - P²₁|) < 1`. -/
noncomputable def prefixKernel (c : ℂ) (P₁ P₂ : Cubic) : ℝ≥0∞ :=
  boxInd P₁ * boxInd P₂ * (ball (-c, (0 : ℂ)) 1).indicator 1 (lamOf P₁ - lamOf P₂)

/-- The prefix kernel is measurable. -/
theorem measurable_prefixKernel (c : ℂ) :
    Measurable fun p : Cubic × Cubic => prefixKernel c p.1 p.2 :=
  ((measurable_boxInd.comp measurable_fst).mul (measurable_boxInd.comp measurable_snd)).mul
    ((measurable_one.indicator measurableSet_ball).comp
      ((measurable_lamOf.comp measurable_fst).sub (measurable_lamOf.comp measurable_snd)))

/-- The prefix kernel is measurable in its second argument. -/
theorem measurable_prefixKernel_left (c : ℂ) (P₁ : Cubic) :
    Measurable fun P₂ => prefixKernel c P₁ P₂ :=
  (measurable_const.mul measurable_boxInd).mul
    ((measurable_one.indicator measurableSet_ball).comp (measurable_const.sub measurable_lamOf))

/-- The near part of the marginal, `m 𝟙{‖λ‖ < 64}`. -/
noncomputable def marginalNear : ℂ × ℂ → ℝ≥0∞ := (ball (0 : ℂ × ℂ) 64).indicator marginal

/-- The far part of the marginal, `m 𝟙{‖λ‖ ≥ 64}`. -/
noncomputable def marginalFar : ℂ × ℂ → ℝ≥0∞ := (ball (0 : ℂ × ℂ) 64)ᶜ.indicator marginal

/-- `m = m_near + m_far`. -/
theorem marginal_le_near_add_far (lam : ℂ × ℂ) :
    marginal lam ≤ marginalNear lam + marginalFar lam := by
  rw [marginalNear, marginalFar, indicator_self_add_compl_apply]

/-- **The translated prefix marginal bound**: `∬ 𝟙{‖λ - μ - z‖ < 1} m(λ) m(μ) ≤ B` for every
`z ∈ ℂ²`, with `B < ∞`. -/
theorem marginal_kernel_bound {C₁ C₂ : ℝ} (hF : LocallyIntegrableF)
    (hK₁ : FullPlaneQuadratic (4 / 3) C₁) (hK₂ : FullPlaneQuadratic (11 / 8) C₂) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ z : ℂ × ℂ,
      ∫⁻ x, ∫⁻ y, (ball z 1).indicator 1 (x - y) * (marginal x * marginal y) ≤ B := by
  have hfn : Measurable marginalNear := measurable_marginal.indicator measurableSet_ball
  have hfa : Measurable marginalFar := measurable_marginal.indicator measurableSet_ball.compl
  have h1 : ∫⁻ x, marginalNear x < ∞ := by
    rw [marginalNear, lintegral_indicator measurableSet_ball]
    exact lintegral_marginal_near_lt_top hF
  have h2 : ∫⁻ x, marginalFar x ^ 2 < ∞ := by
    rw [marginalFar, lintegral_indicator_sq measurableSet_ball.compl]
    exact lintegral_marginal_far_sq_lt_top hK₁ hK₂
  exact ⟨_, kernel_bound_lt_top volume h1 h2, fun z =>
    lintegral_kernel_le volume hfn hfa marginal_le_near_add_far z⟩

/-- The inner prefix integral `ψ_c(P₁) = ∫ F(P₂) K_c(P₁, P₂) dP₂`. -/
noncomputable def prefixInner (c : ℂ) (P₁ : Cubic) : ℝ≥0∞ :=
  ∫⁻ P₂, F P₂ * prefixKernel c P₁ P₂

/-- The inner prefix integral is measurable. -/
theorem measurable_prefixInner (c : ℂ) : Measurable (prefixInner c) :=
  ((measurable_F.comp measurable_snd).mul (measurable_prefixKernel c)).lintegral_prod_right'

/-- The translated convolution `h_z(x) = ∫ 𝟙{‖x - y - z‖ < 1} m(y) dy`. -/
noncomputable def marginalConv (z x : ℂ × ℂ) : ℝ≥0∞ :=
  ∫⁻ y, (ball z 1).indicator 1 (x - y) * marginal y

/-- The translated convolution is measurable. -/
theorem measurable_marginalConv (z : ℂ × ℂ) : Measurable (marginalConv z) :=
  (((measurable_one.indicator measurableSet_ball).comp (measurable_fst.sub measurable_snd)).mul
    (measurable_marginal.comp measurable_snd)).lintegral_prod_right'

/-- The inner prefix integral through the marginal: `ψ_c(P₁) = 𝟙_box(P₁) h_{(-c,0)}(λ(P₁))`. -/
theorem prefixInner_eq (c : ℂ) (P₁ : Cubic) :
    prefixInner c P₁ = boxInd P₁ * marginalConv (-c, 0) (lamOf P₁) := by
  have e : ∀ P₂ : Cubic, F P₂ * prefixKernel c P₁ P₂ =
      boxInd P₁ * (F P₂ * boxInd P₂ *
        (ball ((-c, 0) : ℂ × ℂ) 1).indicator (1 : ℂ × ℂ → ℝ≥0∞) (lamOf P₁ - lamOf P₂)) := by
    intro P₂; rw [prefixKernel]; ring
  have hk : Measurable fun x : ℂ × ℂ =>
      (ball ((-c, 0) : ℂ × ℂ) 1).indicator (1 : ℂ × ℂ → ℝ≥0∞) (lamOf P₁ - x) :=
    (measurable_one.indicator measurableSet_ball).comp (measurable_const.sub measurable_id)
  have hm : Measurable fun P₂ : Cubic => F P₂ * boxInd P₂ *
      (ball ((-c, 0) : ℂ × ℂ) 1).indicator (1 : ℂ × ℂ → ℝ≥0∞) (lamOf P₁ - lamOf P₂) :=
    (measurable_F.mul measurable_boxInd).mul (hk.comp measurable_lamOf)
  rw [prefixInner, lintegral_congr e, lintegral_const_mul _ hm, lintegral_marginal_mul hk,
    marginalConv]
  simp_rw [mul_comm (marginal _)]

/-- **The uniform prefix bound** (the note's `P₃(c) ≤ C B`): the `W₂ ⊗ W₂`-weighted mass of the
position-three prefix constraints is bounded uniformly in the translation `c`. -/
theorem prefix_bound {C C₁ C₂ : ℝ} (hW : WeightedTwoCubeBound C) (hF : LocallyIntegrableF)
    (hK₁ : FullPlaneQuadratic (4 / 3) C₁) (hK₂ : FullPlaneQuadratic (11 / 8) C₂) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ c : ℂ,
      ∫⁻ g₁ : Form × Form, ∫⁻ g₂ : Form × Form, ENNReal.ofReal (W2 g₁) * ENNReal.ofReal (W2 g₂) *
        prefixKernel c (twoCube g₁) (twoCube g₂) ≤ B := by
  obtain ⟨B₀, hB₀, hB⟩ := marginal_kernel_bound hF hK₁ hK₂
  refine ⟨ENNReal.ofReal C * (ENNReal.ofReal C * B₀), by finiteness, fun c => ?_⟩
  have hKl : ∀ P₁ : Cubic, Measurable fun P₂ => prefixKernel c P₁ P₂ :=
    measurable_prefixKernel_left c
  have hw : Measurable fun g : Form × Form => ENNReal.ofReal (W2 g) :=
    measurable_W2.ennreal_ofReal
  -- the inner bound by the two-cube bound
  have step1 : ∀ g₁ : Form × Form, ∫⁻ g₂ : Form × Form, ENNReal.ofReal (W2 g₁) *
      ENNReal.ofReal (W2 g₂) * prefixKernel c (twoCube g₁) (twoCube g₂) ≤
      ENNReal.ofReal C * (ENNReal.ofReal (W2 g₁) * prefixInner c (twoCube g₁)) := by
    intro g₁
    have hm : Measurable fun g₂ : Form × Form =>
        ENNReal.ofReal (W2 g₂) * prefixKernel c (twoCube g₁) (twoCube g₂) :=
      hw.mul ((hKl _).comp measurable_twoCube)
    have e : ∀ g₂ : Form × Form, ENNReal.ofReal (W2 g₁) * ENNReal.ofReal (W2 g₂) *
        prefixKernel c (twoCube g₁) (twoCube g₂) = ENNReal.ofReal (W2 g₁) *
        (ENNReal.ofReal (W2 g₂) * prefixKernel c (twoCube g₁) (twoCube g₂)) :=
      fun g₂ => mul_assoc _ _ _
    rw [lintegral_congr e, lintegral_const_mul _ hm]
    calc ENNReal.ofReal (W2 g₁) * ∫⁻ g₂ : Form × Form, ENNReal.ofReal (W2 g₂) *
          prefixKernel c (twoCube g₁) (twoCube g₂)
        ≤ ENNReal.ofReal (W2 g₁) * (ENNReal.ofReal C * prefixInner c (twoCube g₁)) := by
          gcongr; exact lintegral_W2_twoCube_le hW (hKl _)
      _ = _ := by ring
  have hψ := measurable_prefixInner c
  calc ∫⁻ g₁ : Form × Form, ∫⁻ g₂ : Form × Form, ENNReal.ofReal (W2 g₁) *
        ENNReal.ofReal (W2 g₂) * prefixKernel c (twoCube g₁) (twoCube g₂)
      ≤ ∫⁻ g₁ : Form × Form, ENNReal.ofReal C *
          (ENNReal.ofReal (W2 g₁) * prefixInner c (twoCube g₁)) := lintegral_mono step1
    _ = ENNReal.ofReal C * ∫⁻ g₁ : Form × Form,
          ENNReal.ofReal (W2 g₁) * prefixInner c (twoCube g₁) :=
        lintegral_const_mul _ (hw.mul (hψ.comp measurable_twoCube))
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal C * ∫⁻ P, F P * prefixInner c P) := by
        gcongr; exact lintegral_W2_twoCube_le hW hψ
    _ = ENNReal.ofReal C * (ENNReal.ofReal C * ∫⁻ lam, marginal lam *
          marginalConv (-c, 0) lam) := by
        congr 2
        simp_rw [prefixInner_eq, ← mul_assoc]
        exact lintegral_marginal_mul (measurable_marginalConv _)
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal C * B₀) := by
        gcongr
        refine le_trans (le_of_eq ?_) (hB (-c, 0))
        refine lintegral_congr fun x => ?_
        have hm : Measurable fun y : ℂ × ℂ =>
            (ball ((-c, 0) : ℂ × ℂ) 1).indicator (1 : ℂ × ℂ → ℝ≥0∞) (x - y) * marginal y :=
          ((measurable_one.indicator measurableSet_ball).comp
            (measurable_const.sub measurable_id)).mul measurable_marginal
        rw [marginalConv, ← lintegral_const_mul _ hm]
        refine lintegral_congr fun y => ?_
        ring

end SLT.MiddlePositions.Three
