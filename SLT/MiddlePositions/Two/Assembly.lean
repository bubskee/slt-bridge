/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Two.Suffix
public import SLT.MiddlePositions.Two.Prefix

/-!
# Assembly: the position-two theorem

Section 6 of `complex_middle_positions.tex`, proof of Theorem "Position two". A point of
`Row2 × Row2` is `w = ((l₁, g₁), (l₂, g₂))`: prefix forms `l_k`, suffix form pairs `g_k`, with
prefix cubics `p^k = l_k³` and suffix cubics `q^k = Ψ(g_k)`.

1. `norm_rpow_le_weight`: `‖w‖^{1/4} ≤ V(l₁, l₂) W₂(g₁) W₂(g₂)` (every factor is at least one).
2. `sublevel_indicator_le`: on `‖R₂ w‖ < 1`, the eleven generators put `(l₁, l₂)` in `preSet`,
   `q¹` in the suffix box centred at `-(p¹₀ - p²₀)`, and `q²` in the suffix box centred at `q¹₁`.
3. `lintegral_W2_box_le`: by `WeightedTwoCubeBound` and `setLIntegral_box_F_le`, the `W₂`-weighted
   suffix mass of every unit box is at most `C · Msuf`, uniformly in the centre.
4. `sublevel_two_le`: Tonelli, in the order `g₂`, then `g₁`, then `(l₁, l₂)`, gives
   `∫_{‖R₂‖ < 1} ‖w‖^{1/4} ≤ (C Msuf)² ∫∫ V 𝟙_{preSet}`, and the last integral is finite
   (`lintegral_pre_lt_top`). The headline `sublevelTwo` is in `SLT/MiddlePositions/Two.lean`.

The note instead reduces to `∬_{|Q₁ - Q₂| < 1} N₂(Q₁) N₂(Q₂) P₂(-Q₁)` and applies its Lemma
"Local averaging of a planar bound" with the decay of `N₂` and `P₂`. Here the generator
`p¹₀ - p²₀ + q¹₁` is used only to localise `q¹₁` to a unit disc; no decay in `Q` is used.
-/

@[expose] public section

namespace SLT.MiddlePositions.Two

open MeasureTheory Set Real Metric SLT.PositionFour
open scoped ENNReal NNReal

/-! ### The interface on unit boxes -/

/-- `W₂` is measurable. -/
theorem measurable_W2 : Measurable fun g : Form × Form => ENNReal.ofReal (W2 g) := by
  unfold W2; fun_prop

/-- The two-cube map is measurable. -/
theorem measurable_twoCube' : Measurable twoCube := by unfold twoCube cube; fun_prop

/-- **The interface as an integral inequality**: for measurable `f ≥ 0`,
`∫ W₂(g) f(Ψ(g)) dg ≤ C ∫ F(P) f(P) dP`. -/
theorem lintegral_W2_le {C : ℝ} (hW : WeightedTwoCubeBound C) {f : Cubic → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ g, ENNReal.ofReal (W2 g) * f (twoCube g) ≤ ENNReal.ofReal C * ∫⁻ P, F P * f P := by
  calc ∫⁻ g, ENNReal.ofReal (W2 g) * f (twoCube g)
      = ∫⁻ g, f (twoCube g) ∂((volume : Measure (Form × Form)).withDensity
          fun g => ENNReal.ofReal (W2 g)) :=
        (lintegral_withDensity_eq_lintegral_mul _ measurable_W2 (hf.comp measurable_twoCube')).symm
    _ = ∫⁻ P, f P ∂(((volume : Measure (Form × Form)).withDensity
          fun g => ENNReal.ofReal (W2 g)).map twoCube) :=
        (lintegral_map hf measurable_twoCube').symm
    _ ≤ ∫⁻ P, f P ∂(ENNReal.ofReal C • (volume : Measure Cubic).withDensity F) :=
        lintegral_mono' hW le_rfl
    _ = ENNReal.ofReal C * ∫⁻ P, F P * f P := by
        rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ measurable_F hf]
        rfl

/-- The box indicator is jointly measurable in the centre and the cubic. -/
theorem measurable_box_indicator :
    Measurable fun x : ℂ × Cubic => (box x.1).indicator (1 : Cubic → ℝ≥0∞) x.2 := by
  have hS : MeasurableSet {x : ℂ × Cubic | x.2 ∈ box x.1} := by
    have h1 : MeasurableSet {x : ℂ × Cubic | ‖x.2 1 - x.1‖ < 1} :=
      measurableSet_lt (by fun_prop) measurable_const
    have h2 : MeasurableSet {x : ℂ × Cubic | ‖x.2 2‖ < 1} :=
      measurableSet_lt (by fun_prop) measurable_const
    have h3 : MeasurableSet {x : ℂ × Cubic | ‖x.2 3‖ < 1} :=
      measurableSet_lt (by fun_prop) measurable_const
    exact h1.inter (h2.inter h3)
  have e : (fun x : ℂ × Cubic => (box x.1).indicator (1 : Cubic → ℝ≥0∞) x.2) =
      {x : ℂ × Cubic | x.2 ∈ box x.1}.indicator 1 := by
    funext x
    by_cases h : x.2 ∈ box x.1
    · rw [indicator_of_mem h, indicator_of_mem (show x ∈ {x : ℂ × Cubic | x.2 ∈ box x.1} from h)]
      rfl
    · rw [indicator_of_notMem h,
        indicator_of_notMem (show x ∉ {x : ℂ × Cubic | x.2 ∈ box x.1} from h)]
  rw [e]
  exact measurable_one.indicator hS

/-- **The `W₂`-weighted suffix mass of a unit box is uniformly bounded**: for every `Q₀`,
`∫ W₂(g) 𝟙_{box Q₀}(Ψ(g)) dg ≤ C · Msuf`. -/
theorem lintegral_W2_box_le {C K₀ K₁ K₂ : ℝ} (hW : WeightedTwoCubeBound C)
    (hK₀ : FullPlaneQuadratic (9 / 8) K₀) (hK₁ : FullPlaneQuadratic (4 / 3) K₁)
    (hK₂ : FullPlaneQuadratic (11 / 8) K₂) (hK₀0 : 0 ≤ K₀) (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂)
    (Q₀ : ℂ) :
    ∫⁻ g, ENNReal.ofReal (W2 g) * (box Q₀).indicator 1 (twoCube g) ≤
      ENNReal.ofReal C * ENNReal.ofReal (Msuf K₀ K₁ K₂) := by
  refine (lintegral_W2_le hW (measurable_one.indicator (measurableSet_box Q₀))).trans ?_
  gcongr
  calc ∫⁻ P, F P * (box Q₀).indicator 1 P = ∫⁻ P in box Q₀, F P := by
        rw [← lintegral_indicator (measurableSet_box Q₀)]
        exact lintegral_congr fun P => by rw [mul_comm]; exact indicator_one_mul_eq _ _ P
    _ ≤ _ := setLIntegral_box_F_le hK₀ hK₁ hK₂ hK₀0 hK₁0 hK₂0 Q₀

/-! ### The weight and the sublevel set -/

/-- `(max x y)^p ≤ x^p + y^p` for `x, y, p ≥ 0`. -/
theorem max_rpow_le_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (p : ℝ) :
    max x y ^ p ≤ x ^ p + y ^ p := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]; linarith [Real.rpow_nonneg hx p]
  · rw [max_eq_left h]; linarith [Real.rpow_nonneg hy p]

/-- `‖g‖^{1/4} ≤ W₂(g) - 1`. -/
theorem norm_rpow_le_W2 (g : Form × Form) : ‖g‖ ^ (1 / 4 : ℝ) ≤ W2 g - 1 := by
  have h1 := max_rpow_le_add (norm_nonneg g.1.1) (norm_nonneg g.1.2) (1 / 4)
  have h2 := max_rpow_le_add (norm_nonneg g.2.1) (norm_nonneg g.2.2) (1 / 4)
  have h3 := max_rpow_le_add (norm_nonneg g.1) (norm_nonneg g.2) (1 / 4)
  rw [← Prod.norm_def] at h1 h2
  rw [Prod.norm_def g]
  unfold W2; linarith

/-- **The product weight dominates the weight of the theorem**:
`‖w‖^{1/4} ≤ V(l₁, l₂) W₂(g₁) W₂(g₂)`. -/
theorem norm_rpow_le_weight (w : Row2 × Row2) :
    ‖w‖ ^ (1 / 4 : ℝ) ≤ V w.1.1 w.2.1 * W2 w.1.2 * W2 w.2.2 := by
  have e1 := max_rpow_le_add (norm_nonneg w.1) (norm_nonneg w.2) (1 / 4)
  have e2 := max_rpow_le_add (norm_nonneg w.1.1) (norm_nonneg w.1.2) (1 / 4)
  have e3 := max_rpow_le_add (norm_nonneg w.2.1) (norm_nonneg w.2.2) (1 / 4)
  rw [← Prod.norm_def] at e1
  rw [← Prod.norm_def] at e2 e3
  have f1 := norm_rpow_le_W2 w.1.2
  have f2 := norm_rpow_le_W2 w.2.2
  have hx : 0 ≤ V w.1.1 w.2.1 - 1 := by
    unfold V
    have := Real.rpow_nonneg (norm_nonneg w.1.1) (1 / 4 : ℝ)
    have := Real.rpow_nonneg (norm_nonneg w.2.1) (1 / 4 : ℝ)
    linarith
  have hy : 0 ≤ W2 w.1.2 - 1 := by linarith [one_le_W2 w.1.2]
  have hz : 0 ≤ W2 w.2.2 - 1 := by linarith [one_le_W2 w.2.2]
  have hV : V w.1.1 w.2.1 - 1 = ‖w.1.1‖ ^ (1 / 4 : ℝ) + ‖w.2.1‖ ^ (1 / 4 : ℝ) := by
    unfold V; ring
  nlinarith [mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hx hz,
    mul_nonneg (mul_nonneg hx hy) hz]

/-- The suffix-box integrand of the second suffix row. -/
noncomputable def Bsuf (Q₀ : ℂ) (g : Form × Form) : ℝ≥0∞ :=
  ENNReal.ofReal (W2 g) * (box Q₀).indicator 1 (twoCube g)

/-- `Bsuf` is jointly measurable. -/
theorem measurable_Bsuf : Measurable fun x : ℂ × (Form × Form) => Bsuf x.1 x.2 := by
  unfold Bsuf
  exact (measurable_W2.comp measurable_snd).mul (measurable_box_indicator.comp
    (measurable_fst.prodMk (measurable_twoCube'.comp measurable_snd)))

/-- `Bsuf Q₀` is measurable. -/
theorem measurable_Bsuf_right (Q₀ : ℂ) : Measurable (Bsuf Q₀) := by
  unfold Bsuf
  exact measurable_W2.mul ((measurable_one.indicator (measurableSet_box Q₀)).comp
    measurable_twoCube')

/-- **The sublevel set, generator by generator**: on `‖R₂ w‖ < 1`, the weighted integrand is at
most `pre(l₁, l₂) · Bsuf(-(a₁³ - a₂³), g₁) · Bsuf(q¹₁, g₂)`. -/
theorem sublevel_indicator_le (w : Row2 × Row2) :
    {w : Row2 × Row2 | ‖R2 w‖ < 1}.indicator (fun w => ENNReal.ofReal (‖w‖ ^ (1 / 4 : ℝ))) w ≤
      pre w.1.1 w.2.1 * Bsuf (-(w.1.1.1 ^ 3 - w.2.1.1 ^ 3)) w.1.2 *
        Bsuf (twoCube w.1.2 1) w.2.2 := by
  by_cases hw : w ∈ {w : Row2 × Row2 | ‖R2 w‖ < 1}
  · rw [indicator_of_mem hw]
    obtain ⟨⟨l₁, g₁⟩, ⟨l₂, g₂⟩⟩ := w
    have hc : ∀ i, ‖R2 ((l₁, g₁), (l₂, g₂)) i‖ < 1 := (pi_norm_lt_iff one_pos).mp hw
    have c0 := hc 0
    have c1 := hc 1
    have c2 := hc 2
    have c3 := hc 3
    have c4 := hc 4
    have c5 := hc 5
    have c6 := hc 6
    have c7 := hc 7
    have c8 := hc 8
    have c9 := hc 9
    have c10 := hc 10
    simp only [R2, generators, cube, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
    have hpre : ((l₁, l₂) : Form × Form) ∈ preSet := ⟨c1, c0, c5, c4, c8⟩
    have hb1 : twoCube g₁ ∈ box (-(l₁.1 ^ 3 - l₂.1 ^ 3)) := by
      refine ⟨?_, c2, c3⟩
      rw [sub_neg_eq_add, add_comm]; exact c10
    have hb2 : twoCube g₂ ∈ box (twoCube g₁ 1) := by
      refine ⟨?_, c6, c7⟩
      rw [norm_sub_rev]; exact c9
    simp only [pre, Bsuf, indicator_of_mem hpre, indicator_of_mem hb1, indicator_of_mem hb2,
      Pi.one_apply, mul_one]
    rw [← ENNReal.ofReal_mul (by unfold V; positivity),
      ← ENNReal.ofReal_mul (by unfold V W2; positivity)]
    exact ENNReal.ofReal_le_ofReal (norm_rpow_le_weight _)
  · rw [indicator_of_notMem hw]; exact bot_le

/-! ### Tonelli -/

/-- **The assembled bound**: `∫_{‖R₂‖ < 1} ‖w‖^{1/4} ≤ (C Msuf)² ∫∫ V 𝟙_{preSet}`. -/
theorem sublevel_two_le {C K₀ K₁ K₂ : ℝ} (hW : WeightedTwoCubeBound C)
    (hK₀ : FullPlaneQuadratic (9 / 8) K₀) (hK₁ : FullPlaneQuadratic (4 / 3) K₁)
    (hK₂ : FullPlaneQuadratic (11 / 8) K₂) (hK₀0 : 0 ≤ K₀) (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂) :
    ∫⁻ w in {w : Row2 × Row2 | ‖R2 w‖ < 1}, ENNReal.ofReal (‖w‖ ^ (1 / 4 : ℝ)) ≤
      ENNReal.ofReal C * ENNReal.ofReal (Msuf K₀ K₁ K₂) *
        (ENNReal.ofReal C * ENNReal.ofReal (Msuf K₀ K₁ K₂)) * ∫⁻ l₁, ∫⁻ l₂, pre l₁ l₂ := by
  set M := ENNReal.ofReal C * ENNReal.ofReal (Msuf K₀ K₁ K₂)
  have hM : M ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hbox : ∀ Q₀, ∫⁻ g, Bsuf Q₀ g ≤ M := fun Q₀ =>
    lintegral_W2_box_le hW hK₀ hK₁ hK₂ hK₀0 hK₁0 hK₂0 Q₀
  have hS : MeasurableSet {w : Row2 × Row2 | ‖R2 w‖ < 1} :=
    measurableSet_lt continuous_R2.norm.measurable measurable_const
  -- the joint measurability needed for the swap of `g₁` and `l₂`
  have hswap : ∀ l₁ : Form, AEMeasurable (Function.uncurry fun (g₁ : Form × Form) (l₂ : Form) =>
      pre l₁ l₂ * Bsuf (-(l₁.1 ^ 3 - l₂.1 ^ 3)) g₁ * M) (volume.prod volume) := by
    intro l₁
    refine (((measurable_pre.comp (measurable_const.prodMk measurable_snd)).mul
      (measurable_Bsuf.comp (Measurable.prodMk (by fun_prop) measurable_fst))).mul
        measurable_const).aemeasurable
  rw [← lintegral_indicator hS]
  calc ∫⁻ w, {w : Row2 × Row2 | ‖R2 w‖ < 1}.indicator
        (fun w => ENNReal.ofReal (‖w‖ ^ (1 / 4 : ℝ))) w
      ≤ ∫⁻ w : Row2 × Row2, pre w.1.1 w.2.1 * Bsuf (-(w.1.1.1 ^ 3 - w.2.1.1 ^ 3)) w.1.2 *
          Bsuf (twoCube w.1.2 1) w.2.2 := lintegral_mono sublevel_indicator_le
    _ ≤ ∫⁻ x₁ : Row2, ∫⁻ x₂ : Row2, pre x₁.1 x₂.1 * Bsuf (-(x₁.1.1 ^ 3 - x₂.1.1 ^ 3)) x₁.2 *
          Bsuf (twoCube x₁.2 1) x₂.2 := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_le (fun w : Row2 × Row2 => pre w.1.1 w.2.1 *
          Bsuf (-(w.1.1.1 ^ 3 - w.2.1.1 ^ 3)) w.1.2 * Bsuf (twoCube w.1.2 1) w.2.2)
    _ ≤ ∫⁻ x₁ : Row2, ∫⁻ l₂, ∫⁻ g₂, pre x₁.1 l₂ * Bsuf (-(x₁.1.1 ^ 3 - l₂.1 ^ 3)) x₁.2 *
          Bsuf (twoCube x₁.2 1) g₂ := by
        refine lintegral_mono fun x₁ => ?_
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_le (fun x₂ : Row2 => pre x₁.1 x₂.1 *
          Bsuf (-(x₁.1.1 ^ 3 - x₂.1.1 ^ 3)) x₁.2 * Bsuf (twoCube x₁.2 1) x₂.2)
    _ ≤ ∫⁻ l₁, ∫⁻ g₁, ∫⁻ l₂, ∫⁻ g₂, pre l₁ l₂ * Bsuf (-(l₁.1 ^ 3 - l₂.1 ^ 3)) g₁ *
          Bsuf (twoCube g₁ 1) g₂ := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_le (fun x₁ : Form × (Form × Form) => ∫⁻ l₂, ∫⁻ g₂,
          pre x₁.1 l₂ * Bsuf (-(x₁.1.1 ^ 3 - l₂.1 ^ 3)) x₁.2 * Bsuf (twoCube x₁.2 1) g₂)
    _ ≤ ∫⁻ l₁, ∫⁻ g₁, ∫⁻ l₂, pre l₁ l₂ * Bsuf (-(l₁.1 ^ 3 - l₂.1 ^ 3)) g₁ * M := by
        refine lintegral_mono fun l₁ => lintegral_mono fun g₁ => lintegral_mono fun l₂ => ?_
        rw [lintegral_const_mul _ (measurable_Bsuf_right _)]
        gcongr
        exact hbox _
    _ = ∫⁻ l₁, ∫⁻ l₂, ∫⁻ g₁, pre l₁ l₂ * Bsuf (-(l₁.1 ^ 3 - l₂.1 ^ 3)) g₁ * M :=
        lintegral_congr fun l₁ => lintegral_lintegral_swap (hswap l₁)
    _ ≤ ∫⁻ l₁, ∫⁻ l₂, pre l₁ l₂ * M * M := by
        refine lintegral_mono fun l₁ => lintegral_mono fun l₂ => ?_
        calc ∫⁻ g₁, pre l₁ l₂ * Bsuf (-(l₁.1 ^ 3 - l₂.1 ^ 3)) g₁ * M
            = pre l₁ l₂ * (∫⁻ g₁, Bsuf (-(l₁.1 ^ 3 - l₂.1 ^ 3)) g₁) * M := by
              rw [lintegral_mul_const' _ _ hM, lintegral_const_mul _ (measurable_Bsuf_right _)]
          _ ≤ pre l₁ l₂ * M * M := by gcongr; exact hbox _
    _ = M * M * ∫⁻ l₁, ∫⁻ l₂, pre l₁ l₂ := by
        rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top hM hM)]
        refine lintegral_congr fun l₁ => ?_
        rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top hM hM)]
        refine lintegral_congr fun l₂ => ?_
        ring

end SLT.MiddlePositions.Two
