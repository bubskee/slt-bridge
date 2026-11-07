/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.LLC.Identity
public import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Pointwise LLC limit, abstract half (brief 01, stage L4)

* `antitoneOn_gibbsMean`: `t ↦ E_t[K]` is antitone on `(0, ∞)`. Its derivative is
  `-Var_t[K] ≤ 0`; we get this from mathlib's cumulant generating function, since
  `log Z = cgf (-K) ν`.
* `tendsto_mul_gibbsMean_of_regularVariation`: if `Z` is **regularly varying with index `-λ`**,
  i.e. `Z(at)/Z(t) → a^{-λ}` for every `a > 0`, then `t · E_t[K] → λ`.

Proof of the second: by antitonicity, `∫_t^{at} E = log Z(t) - log Z(at)` lies between
`(a-1) t E(at)` and `(a-1) t E(t)`. So `t E(t)` is squeezed between
`λ log a/(a-1)` and `λ log b/(b-1)` (for `a > 1 > b`) in the limit, and both tend to `λ` as
`a, b → 1`.

Regular variation is **not** proved here for analytic `K`. It needs exact leading-coefficient
asymptotics `Z(t) ~ C t^{-λ} (log t)^{m-1}`, which is strictly more than `HasLaplacePair`
(PLAN.md §4.3). As in `SLT.LLC.Identity`, this is a population, deterministic statement and not
a statement about the SGLD estimator.
-/

@[expose] public section

namespace SLT

open MeasureTheory Filter Topology Real Set ProbabilityTheory

variable {α : Type*} [MeasurableSpace α] {ν : Measure α} {K : α → ℝ} [IsFiniteMeasure ν]

omit [IsFiniteMeasure ν] in
/-- `Zr` is mathlib's moment generating function of `-K`. -/
theorem mgf_neg_eq_Zr (t : ℝ) : mgf (fun x => -K x) ν t = Zr ν K t := by
  simp only [mgf, Zr, mul_neg]

omit [IsFiniteMeasure ν] in
/-- `log Zr` is mathlib's cumulant generating function of `-K`. -/
theorem cgf_neg_eq_log_Zr : cgf (fun x => -K x) ν = fun t => Real.log (Zr ν K t) := by
  funext t; simp only [cgf, mgf_neg_eq_Zr]

private theorem Ioi_subset_interior_integrableExpSet (hK : Measurable K) (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) :
    Ioi 0 ⊆ interior (integrableExpSet (fun x => -K x) ν) := by
  rw [← interior_Ici]
  refine interior_mono fun t ht => ?_
  have := integrable_exp_neg_mul hK hK0 (N := t) ht
  simpa only [integrableExpSet, mem_ofPred_eq, mul_neg] using this

/-- (L1) **`E_t[K]` is antitone** on `(0, ∞)`: `(d/dt) E_t[K] = -Var_t[K] ≤ 0`. -/
theorem antitoneOn_gibbsMean (hK : Measurable K) (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) (hν : ν ≠ 0) :
    AntitoneOn (gibbsMean ν K) (Ioi 0) := by
  set X : α → ℝ := fun x => -K x
  have hsub := Ioi_subset_interior_integrableExpSet hK hK0
  have hE : ∀ t ∈ Ioi (0 : ℝ), gibbsMean ν K t = -deriv (cgf X ν) t := by
    intro t ht
    rw [cgf_neg_eq_log_Zr, (hasDerivAt_log_Zr hK hK0 hν ht).deriv, neg_neg]
  have hmono : MonotoneOn (deriv (cgf X ν)) (Ioi 0) := by
    have hd : DifferentiableOn ℝ (deriv (cgf X ν)) (Ioi 0) := fun t ht =>
      (analyticAt_cgf (hsub ht)).deriv.differentiableAt.differentiableWithinAt
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) hd.continuousOn (by rwa [interior_Ioi]) ?_
    rw [interior_Ioi]
    intro t ht
    have h2 := iteratedDeriv_two_cgf_eq_integral (hsub ht)
    rw [iteratedDeriv_succ, iteratedDeriv_one] at h2
    rw [h2]
    refine div_nonneg (integral_nonneg fun x => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) ?_
    rw [mgf_neg_eq_Zr]
    exact (Zr_pos hK hK0 hν (le_of_lt ht)).le
  intro s hs t ht hst
  rw [hE s hs, hE t ht, neg_le_neg_iff]
  exact hmono hs ht hst

/-- `∫_p^q E ∈ [(q-p) E(q), (q-p) E(p)]` for `0 < p ≤ q`. -/
theorem integral_gibbsMean_bounds (hK : Measurable K) (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x) (hν : ν ≠ 0)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (q - p) * gibbsMean ν K q ≤ Real.log (Zr ν K p) - Real.log (Zr ν K q) ∧
      Real.log (Zr ν K p) - Real.log (Zr ν K q) ≤ (q - p) * gibbsMean ν K p := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hsub : Icc p q ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le hp hs.1
  have hint : IntervalIntegrable (gibbsMean ν K) volume p q :=
    ((continuousOn_gibbsMean hK hK0 hν).mono (by rwa [uIcc_of_le hpq])).intervalIntegrable
  have hanti := antitoneOn_gibbsMean hK hK0 hν
  rw [← integral_gibbsMean hK hK0 hν hp hq]
  constructor
  · have := intervalIntegral.integral_mono_on hpq intervalIntegrable_const hint
      (fun s hs => hanti (hsub hs) hq hs.2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using this
  · have := intervalIntegral.integral_mono_on hpq hint intervalIntegrable_const
      (fun s hs => hanti hp (hsub hs) hs.1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using this

omit [IsFiniteMeasure ν] in
/-- `log a / (a - 1) → 1` as `a → 1`, `a ≠ 1`. -/
private theorem tendsto_log_div_sub_one :
    Tendsto (fun a : ℝ => Real.log a / (a - 1)) (𝓝[≠] 1) (𝓝 1) := by
  have h := hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_log one_ne_zero)
  rw [inv_one] at h
  refine h.congr fun a => ?_
  simp [slope_def_field, Real.log_one]

/-- **L4. Pointwise LLC limit, abstract half**: if `Z` is regularly varying with index `-λ`, then
`t · E_t[K] → λ`. -/
theorem tendsto_mul_gibbsMean_of_regularVariation (hK : Measurable K) (hK0 : ∀ᵐ x ∂ν, 0 ≤ K x)
    (hν : ν ≠ 0) {lam : ℝ}
    (hRV : ∀ a : ℝ, 0 < a → Tendsto (fun t => Zr ν K (a * t) / Zr ν K t) atTop (𝓝 (a ^ (-lam)))) :
    Tendsto (fun t => t * gibbsMean ν K t) atTop (𝓝 lam) := by
  have hZ : ∀ {t : ℝ}, 0 < t → 0 < Zr ν K t := fun ht => Zr_pos hK hK0 hν ht.le
  -- `log Z(at) - log Z(t) → -λ log a`.
  have hlog : ∀ a : ℝ, 0 < a →
      Tendsto (fun t => Real.log (Zr ν K (a * t)) - Real.log (Zr ν K t)) atTop
        (𝓝 (-lam * Real.log a)) := by
    intro a ha
    have := (hRV a ha).log (Real.rpow_pos_of_pos ha _).ne'
    rw [Real.log_rpow ha] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Real.log_div (hZ (mul_pos ha ht)).ne' (hZ ht).ne']
  have hg := tendsto_log_div_sub_one.const_mul lam
  rw [mul_one] at hg
  have hR : 𝓝[>] (1 : ℝ) ≤ 𝓝[≠] 1 :=
    nhdsWithin_mono _ fun a (ha : a ∈ Ioi 1) => mem_compl_singleton_iff.mpr (mem_Ioi.mp ha).ne'
  have hL : 𝓝[<] (1 : ℝ) ≤ 𝓝[≠] 1 :=
    nhdsWithin_mono _ fun a (ha : a ∈ Iio 1) => mem_compl_singleton_iff.mpr (mem_Iio.mp ha).ne
  rw [tendsto_order]
  constructor
  · intro l hl
    -- choose `a > 1` with `λ log a/(a-1) > l`
    obtain ⟨a, hla, ha1⟩ :=
      ((hg.mono_left hR).eventually (lt_mem_nhds hl) |>.and self_mem_nhdsWithin).exists
    have ha1' : (1 : ℝ) < a := ha1
    have hlim := ((hlog a (by linarith)).neg).div_const (a - 1)
    have he : -(-lam * Real.log a) / (a - 1) = lam * (Real.log a / (a - 1)) := by ring
    rw [he] at hlim
    filter_upwards [hlim.eventually (lt_mem_nhds hla), eventually_gt_atTop 0] with t h1 h2
    have hb := (integral_gibbsMean_bounds hK hK0 hν h2 (le_mul_of_one_le_left h2.le ha1'.le)).2
    refine lt_of_lt_of_le h1 ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hb]
  · intro u hu
    obtain ⟨b, hub, hb1⟩ := ((hg.mono_left hL).eventually (gt_mem_nhds hu) |>.and
      (Ioo_mem_nhdsLT zero_lt_one)).exists
    obtain ⟨hb0, hb1'⟩ := hb1
    have hlim := (hlog b hb0).div_const (1 - b)
    have he : -lam * Real.log b / (1 - b) = lam * (Real.log b / (b - 1)) := by
      rw [← neg_sub b 1, div_neg]; ring
    rw [he] at hlim
    filter_upwards [hlim.eventually (gt_mem_nhds hub), eventually_gt_atTop 0] with t h1 h2
    have hbt : 0 < b * t := mul_pos hb0 h2
    have hb := (integral_gibbsMean_bounds hK hK0 hν hbt
      (mul_le_of_le_one_left h2.le hb1'.le)).1
    refine lt_of_le_of_lt ?_ h1
    rw [le_div_iff₀ (by linarith)]
    have : t * gibbsMean ν K t * (1 - b) = (t - b * t) * gibbsMean ν K t := by ring
    linarith

end SLT
