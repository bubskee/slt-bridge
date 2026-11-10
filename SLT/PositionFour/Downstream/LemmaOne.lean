/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Downstream.Marginal

/-!
# Lemma 1: the transverse marginal is in `Lᵖ` away from the origin

`complex_position_four.tex`, Lemma 1: for `0 ≤ β < 2` and `p > 10/(6-β)`,
`m_β 𝟙_{‖λ‖ > 1} ∈ Lᵖ(ℂ²)`, stated here as `∫_{‖λ‖ > 1} m_β^p < ∞` (`lemma_one`).

The proof does not use spherical coordinates. The region `‖λ‖ > 1` is split in two:

* **outer**: `|P₁| ≥ 1`, `6|P₀| ≤ |P₁|²`, `8|P₀|² ≤ |P₁|³`. There `m_β ≲ |P₁|^{β/2-3}` and
  `|P₀| ≤ |P₁|^{3/2}`, so `∫ m_β^p ≲ ∫_{|P₁| > 1/2} |P₁|^{3 - p(3 - β/2)}`, finite iff
  `p(3 - β/2) > 5`, i.e. `p > 10/(6-β)`;
* **central**: the rest. There `|P₀| > 1/9`, `|P₁|³ ≤ 64|P₀|²`, `‖λ‖ ≤ 9|P₀|`, and
  `m_β ≲ |P₀|^{-(2 - β/3 - η/2)}`, so `∫ m_β^p ≲ ∫_{|P₀| > 1/9} |P₀|^{4/3 - p(2 - β/3 - η/2)}`,
  finite iff `p(2 - β/3 - η/2) > 10/3`. This is the note's condition, with the logarithm traded
  for `η`, which is chosen small enough.

The two regions meet at `|P₁| ≍ |P₀|^{2/3}`, the note's transition `|φ| ≍ ε^{1/3}`; both give
exactly the threshold `p > 10/(6-β)`.
-/

@[expose] public section

namespace SLT.PositionFour.Downstream

open MeasureTheory Set Real Metric SLT.Pushforward
open scoped ENNReal NNReal

/-- `{v : |v|ⁿ ≤ r}` lies in the closed disc of radius `r^{1/n}`. -/
theorem subset_closedBall_of_pow_le {n : ℕ} (hn : n ≠ 0) (r : ℝ) :
    {v : ℂ | ‖v‖ ^ n ≤ r} ⊆ closedBall 0 (r ^ ((n : ℝ)⁻¹)) := by
  intro v hv
  rw [mem_closedBall_zero_iff, ← Real.pow_rpow_inv_natCast (norm_nonneg v) hn]
  exact Real.rpow_le_rpow (by positivity) hv (by positivity)

/-- Slabs `{c₀ < |w.1|, |w.2|ⁿ ≤ D |w.1|ᵐ}` are measurable. -/
theorem measurableSet_slab (c₀ D : ℝ) (n m : ℕ) :
    MeasurableSet {w : ℂ × ℂ | c₀ < ‖w.1‖ ∧ ‖w.2‖ ^ n ≤ D * ‖w.1‖ ^ m} :=
  (measurableSet_lt (f := fun _ => c₀) (g := fun w : ℂ × ℂ => ‖w.1‖) measurable_const
    (by fun_prop)).inter
    (measurableSet_le (f := fun w : ℂ × ℂ => ‖w.2‖ ^ n) (g := fun w => D * ‖w.1‖ ^ m)
      (by fun_prop) (by fun_prop))

/-- **A slab integral on `ℂ²`**: for `c₀ > 0`, `n ≠ 0` and `γ - 2m/n > 2`,
`∫ 𝟙{c₀ < |u|, |v|ⁿ ≤ D |u|ᵐ} C |u|^{-γ} du dv < ∞`. -/
theorem lintegral_slab_lt_top {c₀ C D γ : ℝ} {n m : ℕ} (hc₀ : 0 < c₀) (hn : n ≠ 0)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hγ : 2 < γ - 2 * m / n) :
    ∫⁻ w : ℂ × ℂ, {w : ℂ × ℂ | c₀ < ‖w.1‖ ∧ ‖w.2‖ ^ n ≤ D * ‖w.1‖ ^ m}.indicator
      (fun w => ENNReal.ofReal (C * ‖w.1‖ ^ (-γ))) w < ∞ := by
  set S := {w : ℂ × ℂ | c₀ < ‖w.1‖ ∧ ‖w.2‖ ^ n ≤ D * ‖w.1‖ ^ m}
  have hS : MeasurableSet S := measurableSet_slab c₀ D n m
  set γ' := γ - 2 * m / n
  set K := C * D ^ (2 / (n : ℝ)) * π
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have slice : ∀ u : ℂ, ∫⁻ v, S.indicator (fun w => ENNReal.ofReal (C * ‖w.1‖ ^ (-γ))) (u, v) ≤
      {u : ℂ | c₀ < ‖u‖}.indicator (fun u => ENNReal.ofReal K * ‖u‖ₑ⁻¹ ^ γ') u := by
    intro u
    by_cases hu : c₀ < ‖u‖
    · have hu0 : 0 < ‖u‖ := hc₀.trans hu
      rw [indicator_of_mem (show u ∈ {u : ℂ | c₀ < ‖u‖} from hu)]
      have e : (fun v => S.indicator (fun w => ENNReal.ofReal (C * ‖w.1‖ ^ (-γ))) (u, v)) =
          {v : ℂ | ‖v‖ ^ n ≤ D * ‖u‖ ^ m}.indicator
            (fun _ => ENNReal.ofReal (C * ‖u‖ ^ (-γ))) := by
        funext v; simp [S, indicator, hu]
      have hr : 0 ≤ D * ‖u‖ ^ m := by positivity
      rw [e, lintegral_indicator_const (measurableSet_le (by fun_prop) measurable_const)]
      calc ENNReal.ofReal (C * ‖u‖ ^ (-γ)) * volume {v : ℂ | ‖v‖ ^ n ≤ D * ‖u‖ ^ m}
          ≤ ENNReal.ofReal (C * ‖u‖ ^ (-γ)) *
              volume (closedBall (0 : ℂ) ((D * ‖u‖ ^ m) ^ ((n : ℝ)⁻¹))) := by
            gcongr; exact subset_closedBall_of_pow_le hn _
        _ = ENNReal.ofReal K * ‖u‖ₑ⁻¹ ^ γ' := by
            rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow (by positivity),
              show ((NNReal.pi : ℝ≥0∞)) = ENNReal.ofReal π by
                rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi],
              ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
              enorm_inv_rpow_of_ne_zero (norm_pos_iff.mp hu0),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hr, Real.mul_rpow hD (by positivity),
              ← Real.rpow_natCast ‖u‖ m, ← Real.rpow_mul hu0.le]
            have e1 : ‖u‖ ^ (-γ) * ‖u‖ ^ ((m : ℝ) * ((n : ℝ)⁻¹ * ((2 : ℕ) : ℝ))) =
                ‖u‖ ^ (-γ') := by
              rw [← Real.rpow_add hu0]; congr 1; simp only [γ']; push_cast; field_simp; ring
            have e2 : (n : ℝ)⁻¹ * ((2 : ℕ) : ℝ) = 2 / n := by push_cast; ring
            simp only [K]
            rw [← e1, e2]; ring
    · rw [indicator_of_notMem (show u ∉ {u : ℂ | c₀ < ‖u‖} from hu)]
      refine le_of_eq (lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun v => ?_))
      exact indicator_of_notMem (fun h => hu h.1) _
  rw [Measure.volume_eq_prod, lintegral_prod _ ((by fun_prop :
    Measurable fun w : ℂ × ℂ => ENNReal.ofReal (C * ‖w.1‖ ^ (-γ))).indicator hS).aemeasurable]
  refine lt_of_le_of_lt (lintegral_mono slice) ?_
  rw [lintegral_indicator (measurableSet_lt measurable_const measurable_norm),
    lintegral_const_mul _ (by fun_prop), lintegral_norm_gt_inv_rpow hγ hc₀]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- The same slab with the roles of the two coordinates exchanged. -/
theorem lintegral_slab_swap_lt_top {c₀ C D γ : ℝ} {n m : ℕ} (hc₀ : 0 < c₀) (hn : n ≠ 0)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hγ : 2 < γ - 2 * m / n) :
    ∫⁻ w : ℂ × ℂ, {w : ℂ × ℂ | c₀ < ‖w.2‖ ∧ ‖w.1‖ ^ n ≤ D * ‖w.2‖ ^ m}.indicator
      (fun w => ENNReal.ofReal (C * ‖w.2‖ ^ (-γ))) w < ∞ := by
  have h := lintegral_slab_lt_top hc₀ hn hC hD hγ
  rw [Measure.volume_eq_prod, ← lintegral_prod_swap] at h
  rw [Measure.volume_eq_prod]
  refine lt_of_eq_of_lt ?_ h
  congr 1

/-! ### The two regions -/

/-- The outer region `|P₁| ≥ 1`, `6|P₀| ≤ |P₁|²`, `8|P₀|² ≤ |P₁|³`. -/
def outerRegion : Set (ℂ × ℂ) :=
  {lam | 1 ≤ ‖lam.2‖ ∧ 6 * ‖lam.1‖ ≤ ‖lam.2‖ ^ 2 ∧ 8 * ‖lam.1‖ ^ 2 ≤ ‖lam.2‖ ^ 3}

/-- Off the outer region, `‖λ‖ > 1` forces `|P₀| > 1/9` and `|P₁|³ ≤ 64 |P₀|²`. -/
theorem central_facts {lam : ℂ × ℂ} (h1 : 1 < ‖lam‖) (hout : lam ∉ outerRegion) :
    1 / 9 < ‖lam.1‖ ∧ ‖lam.2‖ ^ 3 ≤ 64 * ‖lam.1‖ ^ 2 := by
  have hx := norm_nonneg lam.1
  have hy := norm_nonneg lam.2
  have hmax : 1 < max ‖lam.1‖ ‖lam.2‖ := by rwa [Prod.norm_def] at h1
  simp only [outerRegion, mem_ofPred_eq, not_and_or, not_le] at hout
  rcases lt_or_ge ‖lam.2‖ 1 with hy1 | hy1
  · have hx1 : 1 < ‖lam.1‖ := by
      rcases le_total ‖lam.1‖ ‖lam.2‖ with h | h
      · rw [max_eq_right h] at hmax; linarith
      · rwa [max_eq_left h] at hmax
    refine ⟨by linarith, ?_⟩
    have : ‖lam.2‖ ^ 3 ≤ 1 := pow_le_one₀ hy hy1.le
    nlinarith
  · rcases hout with h | h | h
    · linarith
    · -- `y² < 6x`
      have hx6 : 1 / 6 < ‖lam.1‖ := by nlinarith
      refine ⟨by linarith, ?_⟩
      have h6 : (‖lam.2‖ ^ 2) ^ 3 ≤ (6 * ‖lam.1‖) ^ 3 := pow_le_pow_left₀ (by positivity) h.le 3
      have hsq : (‖lam.2‖ ^ 3) ^ 2 ≤ (64 * ‖lam.1‖ ^ 2) ^ 2 := by nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
    · -- `y³ < 8x²`
      have hx2 := sq_nonneg ‖lam.1‖
      have hy3 : 1 ≤ ‖lam.2‖ ^ 3 := one_le_pow₀ hy1
      refine ⟨?_, by linarith⟩
      nlinarith

/-- In the central region, `|P₁| ≤ 9 |P₀|`. -/
theorem norm_snd_le_of_central {lam : ℂ × ℂ} (hx : 1 / 9 < ‖lam.1‖)
    (hy : ‖lam.2‖ ^ 3 ≤ 64 * ‖lam.1‖ ^ 2) : ‖lam.2‖ ≤ 9 * ‖lam.1‖ := by
  by_contra h
  replace h := not_le.mp h
  have h0 : 0 ≤ 9 * ‖lam.1‖ := by positivity
  have : (9 * ‖lam.1‖) ^ 3 < ‖lam.2‖ ^ 3 := pow_lt_pow_left₀ h h0 (by norm_num)
  nlinarith

/-- **Lemma 1** (`complex_position_four.tex`). For `0 ≤ β < 2` and `p > 10/(6-β)`, the transverse
marginal restricted to `‖λ‖ > 1` has finite `Lᵖ` norm:
`∫_{‖λ‖ > 1} m_β(λ)^p dλ < ∞`. -/
theorem lemma_one {β p : ℝ} (hβ0 : 0 ≤ β) (hβ2 : β < 2) (hp : 10 / (6 - β) < p) :
    ∫⁻ lam in {lam : ℂ × ℂ | 1 < ‖lam‖}, transverseMarginal β lam ^ p < ∞ := by
  have h6 : 0 < 6 - β := by linarith
  have hp0 : 0 < p := lt_of_le_of_lt (by positivity) hp
  have hpβ : 10 < p * (6 - β) := by rwa [div_lt_iff₀ h6] at hp
  -- the slack `η`
  set g := 2 - β / 3 - 10 / (3 * p) with hg
  have hg0 : 0 < g := by
    rw [hg, sub_pos, div_lt_iff₀ (by positivity)]; nlinarith
  set η := min (1 / 2) g with hη
  have hη0 : 0 < η := lt_min (by norm_num) hg0
  have hη1 : η ≤ 1 / 2 := min_le_left _ _
  have hηg : η ≤ g := min_le_right _ _
  obtain ⟨Kc, hKc0, hKc⟩ := transverseMarginal_le_central hβ0 hβ2 hη0 hη1
  obtain ⟨Ko, hKo0, hKo⟩ := transverseMarginal_le_outer hβ0 hβ2
  set e := 2 - β / 3 - η / 2 with he
  set K' := Kc * (9 ^ (β / 3) + 1 + 19 ^ (β / 2)) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  -- the two majorants
  set Fc : ℂ × ℂ → ℝ≥0∞ :=
    {w : ℂ × ℂ | 1 / 9 < ‖w.1‖ ∧ ‖w.2‖ ^ 3 ≤ 64 * ‖w.1‖ ^ 2}.indicator
      (fun w => ENNReal.ofReal (K' ^ p * ‖w.1‖ ^ (-(e * p))))
  set Fo : ℂ × ℂ → ℝ≥0∞ :=
    {w : ℂ × ℂ | 1 / 2 < ‖w.2‖ ∧ ‖w.1‖ ^ 2 ≤ 1 * ‖w.2‖ ^ 3}.indicator
      (fun w => ENNReal.ofReal (Ko ^ p * ‖w.2‖ ^ (-((3 - β / 2) * p))))
  have hFc : ∫⁻ w, Fc w < ∞ :=
    lintegral_slab_lt_top (by norm_num) (by norm_num) (by positivity) (by norm_num) (by
      push_cast
      have : 10 / 3 < e * p := by
        have h3p : 10 / (3 * p) * p = 10 / 3 := by field_simp
        nlinarith
      linarith)
  have hFo : ∫⁻ w, Fo w < ∞ :=
    lintegral_slab_swap_lt_top (by norm_num) (by norm_num) (by positivity) (by norm_num) (by
      push_cast; nlinarith)
  have hFcm : Measurable Fc :=
    (by fun_prop : Measurable fun w : ℂ × ℂ =>
      ENNReal.ofReal (K' ^ p * ‖w.1‖ ^ (-(e * p)))).indicator
      (measurableSet_slab _ _ _ _)
  -- the pointwise bound
  have hpt : ∀ lam ∈ {lam : ℂ × ℂ | 1 < ‖lam‖}, transverseMarginal β lam ^ p ≤ Fc lam + Fo lam := by
    intro lam hlam
    rw [mem_ofPred_eq] at hlam
    by_cases hout : lam ∈ outerRegion
    · obtain ⟨h1, h6', h8⟩ := hout
      have hy0 : 0 < ‖lam.2‖ := by linarith
      refine le_add_left (le_of_le_of_eq (ENNReal.rpow_le_rpow (hKo lam h1 h6' h8) hp0.le) ?_)
      have hmem : lam ∈ {w : ℂ × ℂ | 1 / 2 < ‖w.2‖ ∧ ‖w.1‖ ^ 2 ≤ 1 * ‖w.2‖ ^ 3} :=
        ⟨by linarith, by nlinarith⟩
      simp only [Fo, indicator_of_mem hmem]
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le,
        Real.mul_rpow hKo0 (by positivity), ← Real.rpow_mul hy0.le]
      congr 3; ring
    · obtain ⟨hx9, hy64⟩ := central_facts hlam hout
      have hx0 : 0 < ‖lam.1‖ := by linarith
      have hP₀ : lam.1 ≠ 0 := norm_pos_iff.mp hx0
      have hy9 := norm_snd_le_of_central hx9 hy64
      have hnorm : ‖lam‖ ≤ 9 * ‖lam.1‖ := by
        rw [Prod.norm_def]; exact max_le (by linarith) hy9
      have hN : ‖lam.1‖ + ‖lam.2‖ + 1 ≤ 19 * ‖lam.1‖ := by linarith
      have hbound : transverseMarginal β lam ≤ ENNReal.ofReal (K' * ‖lam.1‖ ^ (-e)) := by
        refine (hKc lam hP₀ hlam.le).trans (ENNReal.ofReal_le_ofReal ?_)
        -- each term is at most a constant times `|P₀|^{-e}`
        set x := ‖lam.1‖
        have t1 : ‖lam‖ ^ (β / 3) * x ^ (-2 + η / 2) ≤ 9 ^ (β / 3) * x ^ (-e) := by
          calc ‖lam‖ ^ (β / 3) * x ^ (-2 + η / 2)
              ≤ (9 * x) ^ (β / 3) * x ^ (-2 + η / 2) := by gcongr
            _ = 9 ^ (β / 3) * x ^ (-e) := by
                rw [Real.mul_rpow (by norm_num) hx0.le, mul_assoc, ← Real.rpow_add hx0, he]
                ring_nf
        have t2 : x ^ (-2 + β / 3 + η / 2) = 1 * x ^ (-e) := by rw [he, one_mul]; ring_nf
        have t3 : (x + ‖lam.2‖ + 1) ^ (β / 2) * x ^ (-2 - β / 6 + η / 2) ≤
            19 ^ (β / 2) * x ^ (-e) := by
          calc (x + ‖lam.2‖ + 1) ^ (β / 2) * x ^ (-2 - β / 6 + η / 2)
              ≤ (19 * x) ^ (β / 2) * x ^ (-2 - β / 6 + η / 2) := by gcongr
            _ = 19 ^ (β / 2) * x ^ (-e) := by
                rw [Real.mul_rpow (by norm_num) hx0.le, mul_assoc, ← Real.rpow_add hx0, he]
                ring_nf
        rw [hK', mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hKc0
        rw [add_mul, add_mul]
        linarith
      refine le_add_right (le_of_le_of_eq (ENNReal.rpow_le_rpow hbound hp0.le) ?_)
      have hmem : lam ∈ {w : ℂ × ℂ | 1 / 9 < ‖w.1‖ ∧ ‖w.2‖ ^ 3 ≤ 64 * ‖w.1‖ ^ 2} :=
        ⟨hx9, hy64⟩
      simp only [Fc, indicator_of_mem hmem]
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le,
        Real.mul_rpow hK'0 (by positivity), ← Real.rpow_mul hx0.le]
      congr 3; ring
  calc ∫⁻ lam in {lam : ℂ × ℂ | 1 < ‖lam‖}, transverseMarginal β lam ^ p
      ≤ ∫⁻ lam in {lam : ℂ × ℂ | 1 < ‖lam‖}, (Fc lam + Fo lam) :=
        setLIntegral_mono' (measurableSet_lt measurable_const measurable_norm) hpt
    _ ≤ ∫⁻ lam, (Fc lam + Fo lam) := setLIntegral_le_lintegral _ _
    _ < ∞ := by
        rw [lintegral_add_left hFcm]
        exact ENNReal.add_lt_top.mpr ⟨hFc, hFo⟩

end SLT.PositionFour.Downstream
