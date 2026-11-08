/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Template.Elementary
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The elementary template, part 2: critical weights on a pivot cone (brief 03, T1)

The **pivot cone** in `ℝ × ℝⁿ` is `{(r, p) | |r| ≤ ε, |pᵢ| ≤ |r| for all i}`. Take a weight `w`
of critical homogeneity on it, with an angular part that may depend on the radius:

`w (r, r • q) = |r|^{-(n+1)} h_r(q)` for `q ∈ [-1,1]ⁿ`, with `∫_{[-1,1]ⁿ} h_r ≤ H` uniformly in `r`.

Then `w` satisfies the logarithmic min-integral bound (`minLogBound_pivotCone`):
`∫_cone min (T, s · w) ≤ 2 s H (1 + log⁺ ε + log⁺ (2ⁿ T / H) + log⁺ (1/s))`.

This is cubic-chaos Theorem M's Lemma M5 in general form ("uniform integrability of `|det|^{-1/2}`
plus the radial split gives one extra log"). There, `n = 2`, `r = a_p` is the pivot amplitude,
`q = (a_i/a_p, a_j/a_p)`, and `h_r = |q a' E_r|^{-1/2}` with Lemma M3's uniform bound.

The weight need not be weak-L¹ when `h_r` really depends on `r`, so the bound is stated for the
min-integral directly. The proof rescales each fibre linearly (`Measure.map_addHaar_smul`), bounds
the angular integral by `min (2ⁿ T, s |r|^{-(n+1)} H)`, and splits the radial integral.
-/

@[expose] public section

namespace SLT.Template

open MeasureTheory Set Real
open scoped ENNReal

/-- The pivot cone `{(r, p) | |r| ≤ ε, |pᵢ| ≤ |r| ∀ i}` in `ℝ × ℝⁿ`. -/
def pivotCone (n : ℕ) (ε : ℝ) : Set (ℝ × (Fin n → ℝ)) :=
  {x | |x.1| ≤ ε ∧ ∀ i, |x.2 i| ≤ |x.1|}

/-- The pivot cone is measurable. -/
theorem measurableSet_pivotCone (n : ℕ) (ε : ℝ) : MeasurableSet (pivotCone n ε) := by
  unfold pivotCone
  simp only [ofPred_and, ofPred_forall]
  refine (measurableSet_le (by fun_prop) measurable_const).inter
    (MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) (by fun_prop))

/-- Linear rescaling of a lintegral on `ℝⁿ`: `∫ f = |r|ⁿ ∫ f (r • q) dq` for `r ≠ 0`. -/
theorem lintegral_eq_smul_rescale {n : ℕ} {f : (Fin n → ℝ) → ℝ≥0∞} (hf : Measurable f) {r : ℝ}
    (hr : r ≠ 0) : ∫⁻ p, f p = ENNReal.ofReal (|r| ^ n) * ∫⁻ q, f (r • q) := by
  rw [← lintegral_map hf (measurable_const_smul r), Measure.map_addHaar_smul volume hr,
    lintegral_smul_measure, Module.finrank_fin_fun, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), abs_inv, abs_pow, mul_inv_cancel₀ (by positivity),
    ENNReal.ofReal_one, one_mul]

/-- The radial step: `∫_{[-ε,ε]} min (a |r|ⁿ, c/|r|) dr ≤ 2c (1 + log⁺ ε + log⁺ (a/c))`. -/
theorem lintegral_min_pow_div_le (n : ℕ) {a c ε : ℝ} (ha : 0 < a) (hc : 0 < c) (hε : 0 < ε) :
    ∫⁻ r : ℝ, (Icc (-ε) ε).indicator
      (fun r => min (ENNReal.ofReal (a * |r| ^ n)) (ENNReal.ofReal (c / |r|))) r ≤
      ENNReal.ofReal (2 * c * (1 + Real.posLog ε + Real.posLog (a / c))) := by
  set φ : ℝ → ℝ≥0∞ := (Icc (-ε) ε).indicator
    (fun r => min (ENNReal.ofReal (a * |r| ^ n)) (ENNReal.ofReal (c / |r|))) with hφ
  have hφm : Measurable φ := (by fun_prop : Measurable fun r : ℝ =>
    min (ENNReal.ofReal (a * |r| ^ n)) (ENNReal.ofReal (c / |r|))).indicator measurableSet_Icc
  set ψ : ℝ → ℝ≥0∞ := (Ici 0).indicator φ with hψ
  have hψm : Measurable ψ := hφm.indicator measurableSet_Ici
  have hφeven : ∀ r, φ (-r) = φ r := by
    intro r
    have hmem : -r ∈ Icc (-ε) ε ↔ r ∈ Icc (-ε) ε := by
      simp only [mem_Icc, neg_le_neg_iff, neg_le]; exact and_comm
    by_cases hr : r ∈ Icc (-ε) ε
    · rw [hφ, indicator_of_mem (hmem.mpr hr), indicator_of_mem hr, abs_neg]
    · rw [hφ, indicator_of_notMem (fun h => hr (hmem.mp h)), indicator_of_notMem hr]
  have hφψ : ∀ r, φ r ≤ ψ r + ψ (-r) := by
    intro r
    rcases le_total 0 r with h | h
    · rw [hψ, indicator_of_mem (show r ∈ Ici 0 from h)]; exact le_self_add
    · rw [hψ, indicator_of_mem (show -r ∈ Ici 0 from neg_nonneg.mpr h), hφeven]
      exact le_add_self
  have hneg : ∫⁻ r, ψ (-r) = ∫⁻ r, ψ r :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp hψm
  -- the half line
  set ρ0 := min (min ε 1) (c / a) with hρ0def
  have hρ0 : 0 < ρ0 := lt_min (lt_min hε one_pos) (div_pos hc ha)
  have hρε : ρ0 ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hρ1 : ρ0 ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hρca : ρ0 ≤ c / a := min_le_right _ _
  have hψle : ∀ r, ψ r ≤ (Icc 0 ρ0).indicator (fun _ => ENNReal.ofReal (a * ρ0 ^ n)) r +
      (Ioc ρ0 ε).indicator (fun r => ENNReal.ofReal (c / r)) r := by
    intro r
    by_cases h0 : 0 ≤ r
    · by_cases hrε : r ≤ ε
      · have hφr : φ r = min (ENNReal.ofReal (a * |r| ^ n)) (ENNReal.ofReal (c / |r|)) :=
          indicator_of_mem (show r ∈ Icc (-ε) ε from ⟨by linarith, hrε⟩) _
        rw [hψ, indicator_of_mem (show r ∈ Ici 0 from h0), hφr, abs_of_nonneg h0]
        by_cases hr : r ≤ ρ0
        · rw [indicator_of_mem (show r ∈ Icc 0 ρ0 from ⟨h0, hr⟩)]
          refine (min_le_left _ _).trans (le_trans ?_ le_self_add)
          exact ENNReal.ofReal_le_ofReal (by gcongr)
        · rw [indicator_of_mem (show r ∈ Ioc ρ0 ε from ⟨not_le.mp hr, hrε⟩)]
          exact (min_le_right _ _).trans le_add_self
      · have : φ r = 0 := indicator_of_notMem (fun h => hrε h.2) _
        rw [hψ, indicator_of_mem (show r ∈ Ici 0 from h0), this]; exact zero_le
    · rw [hψ, indicator_of_notMem (show r ∉ Ici 0 from h0)]; exact zero_le
  have hhalf : ∫⁻ r, ψ r ≤ ENNReal.ofReal (a * ρ0 ^ n * ρ0) +
      ENNReal.ofReal (c * Real.log (ε / ρ0)) := by
    calc ∫⁻ r, ψ r ≤ ∫⁻ r, ((Icc 0 ρ0).indicator (fun _ => ENNReal.ofReal (a * ρ0 ^ n)) r +
          (Ioc ρ0 ε).indicator (fun r => ENNReal.ofReal (c / r)) r) := lintegral_mono hψle
      _ = (∫⁻ r, (Icc 0 ρ0).indicator (fun _ => ENNReal.ofReal (a * ρ0 ^ n)) r) +
          ∫⁻ r, (Ioc ρ0 ε).indicator (fun r => ENNReal.ofReal (c / r)) r :=
          lintegral_add_left (measurable_const.indicator measurableSet_Icc) _
      _ = _ := by
          rw [lintegral_indicator measurableSet_Icc, lintegral_indicator measurableSet_Ioc,
            setLIntegral_const, Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul (by positivity),
            lintegral_Ioc_div hρ0 hρε hc.le]
  -- the logarithm
  have hlog : Real.log (ε / ρ0) ≤ Real.posLog ε + Real.posLog (a / c) := by
    have hx0 : 0 < min ε 1 := lt_min hε one_pos
    have hy : min 1 (c / a) ≤ 1 := min_le_left _ _
    have hxy : min ε 1 * min 1 (c / a) ≤ ρ0 := by
      refine le_min ?_ ?_
      · exact mul_le_of_le_one_right hx0.le hy
      · calc min ε 1 * min 1 (c / a) ≤ 1 * min 1 (c / a) := by gcongr; exact min_le_right _ _
          _ ≤ c / a := by rw [one_mul]; exact min_le_right _ _
    have e1 : max 1 ε * min ε 1 = ε := by
      rcases le_total ε 1 with h | h
      · rw [max_eq_left h, min_eq_left h, one_mul]
      · rw [max_eq_right h, min_eq_right h, mul_one]
    have e2 : max 1 (a / c) * min 1 (c / a) = 1 := by
      rcases le_total (a / c) 1 with h | h
      · have : 1 ≤ c / a := by
          rw [div_le_one hc] at h; rw [one_le_div ha]; exact h
        rw [max_eq_left h, min_eq_left this, one_mul]
      · have : c / a ≤ 1 := by
          rw [one_le_div hc] at h; rw [div_le_one ha]; exact h
        rw [max_eq_right h, min_eq_right this]; field_simp
    have h1 : ε / ρ0 ≤ max 1 ε * max 1 (a / c) := by
      rw [div_le_iff₀ hρ0]
      calc ε = max 1 ε * max 1 (a / c) * (min ε 1 * min 1 (c / a)) := by
            calc ε = (max 1 ε * min ε 1) * (max 1 (a / c) * min 1 (c / a)) := by
                  rw [e1, e2, mul_one]
              _ = _ := by ring
        _ ≤ max 1 ε * max 1 (a / c) * ρ0 := by gcongr
    calc Real.log (ε / ρ0) ≤ Real.log (max 1 ε * max 1 (a / c)) :=
          Real.log_le_log (div_pos hε hρ0) h1
      _ = Real.log (max 1 ε) + Real.log (max 1 (a / c)) :=
          Real.log_mul (by positivity) (by positivity)
      _ = Real.posLog ε + Real.posLog (a / c) := by
          rw [Real.posLog_eq_log_max_one hε.le, Real.posLog_eq_log_max_one (by positivity)]
  calc ∫⁻ r, φ r ≤ ∫⁻ r, (ψ r + ψ (-r)) := lintegral_mono hφψ
    _ = (∫⁻ r, ψ r) + ∫⁻ r, ψ (-r) := lintegral_add_left hψm _
    _ = 2 * ∫⁻ r, ψ r := by rw [hneg, two_mul]
    _ ≤ 2 * (ENNReal.ofReal (a * ρ0 ^ n * ρ0) + ENNReal.ofReal (c * Real.log (ε / ρ0))) := by
        gcongr
    _ ≤ ENNReal.ofReal (2 * c * (1 + Real.posLog ε + Real.posLog (a / c))) := by
        have hl0 : 0 ≤ Real.log (ε / ρ0) := Real.log_nonneg ((one_le_div hρ0).mpr hρε)
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        have e1 : a * ρ0 ^ n * ρ0 ≤ c := by
          have : ρ0 ^ n ≤ 1 := pow_le_one₀ hρ0.le hρ1
          calc a * ρ0 ^ n * ρ0 ≤ a * 1 * (c / a) := by gcongr
            _ = c := by field_simp
        have e2 := mul_le_mul_of_nonneg_left hlog hc.le
        nlinarith

/-- **Critical weights on a pivot cone (Theorem M's M5, general form).** Let
`w (r, r • q) = |r|^{-(n+1)} h_r(q)` for `0 < |r| ≤ ε` and `q ∈ [-1,1]ⁿ`, where
`∫_{[-1,1]ⁿ} h_r ≤ H` for every such `r`. Then on the pivot cone `w` satisfies the logarithmic
min-integral bound with `B = 2H (1 + log⁺ ε + log⁺ (2ⁿ T / H))` and `D = 2H`. -/
theorem minLogBound_pivotCone {n : ℕ} {ε : ℝ} (hε : 0 < ε) {w : ℝ × (Fin n → ℝ) → ℝ≥0∞}
    (hw : Measurable w) {h : ℝ → (Fin n → ℝ) → ℝ≥0∞} {H T : ℝ} (hH0 : 0 < H) (hT : 0 < T)
    (hH : ∀ r : ℝ, r ≠ 0 → |r| ≤ ε → ∫⁻ q in Icc (-1 : Fin n → ℝ) 1, h r q ≤ ENNReal.ofReal H)
    (hhom : ∀ r : ℝ, r ≠ 0 → |r| ≤ ε → ∀ q ∈ Icc (-1 : Fin n → ℝ) 1,
      w (r, r • q) = ENNReal.ofReal (|r|⁻¹ ^ (n + 1)) * h r q) :
    MinLogBound (volume.restrict (pivotCone n ε)) w T
      (2 * H * (1 + Real.posLog ε + Real.posLog (2 ^ n * T / H))) (2 * H) := by
  intro s hs
  set g : ℝ × (Fin n → ℝ) → ℝ≥0∞ := fun x => min (ENNReal.ofReal T) (ENNReal.ofReal s * w x)
  have hgm : Measurable g := measurable_const.min (measurable_const.mul hw)
  set a := 2 ^ n * T with ha_def
  set c := s * H with hc_def
  have ha : 0 < a := by positivity
  have hc : 0 < c := mul_pos hs hH0
  set φ1 : ℝ → ℝ≥0∞ := (Icc (-ε) ε).indicator
    (fun r => min (ENNReal.ofReal (a * |r| ^ n)) (ENNReal.ofReal (c / |r|)))
  -- fibrewise
  have hfib : ∀ r : ℝ, r ≠ 0 → ∫⁻ p, (pivotCone n ε).indicator g (r, p) ≤ φ1 r := by
    intro r hr
    have hr0 : 0 < |r| := abs_pos.mpr hr
    have hmr : Measurable fun p : Fin n → ℝ => (pivotCone n ε).indicator g (r, p) :=
      (hgm.indicator (measurableSet_pivotCone n ε)).comp measurable_prodMk_left
    by_cases hrε : |r| ≤ ε
    · rw [lintegral_eq_smul_rescale hmr hr]
      have hcone : ∀ q : Fin n → ℝ,
          (r, r • q) ∈ pivotCone n ε ↔ q ∈ Icc (-1 : Fin n → ℝ) 1 := by
        intro q
        simp only [pivotCone, mem_ofPred_eq, mem_Icc, Pi.le_def, Pi.neg_apply, Pi.one_apply,
          Pi.smul_apply, smul_eq_mul, hrε, true_and, ← forall_and]
        refine forall_congr' fun i => ?_
        rw [abs_mul, ← abs_le, mul_le_iff_le_one_right hr0]
      have hpt : ∀ q, (pivotCone n ε).indicator g (r, r • q) = (Icc (-1 : Fin n → ℝ) 1).indicator
          (fun q => min (ENNReal.ofReal T)
            (ENNReal.ofReal (s * |r|⁻¹ ^ (n + 1)) * h r q)) q := by
        intro q
        by_cases hq : q ∈ Icc (-1 : Fin n → ℝ) 1
        · rw [indicator_of_mem ((hcone q).mpr hq), indicator_of_mem hq]
          simp only [g]
          rw [hhom r hr hrε q hq, ← mul_assoc, ← ENNReal.ofReal_mul hs.le]
        · rw [indicator_of_notMem (fun h' => hq ((hcone q).mp h')), indicator_of_notMem hq]
      simp_rw [hpt]
      rw [lintegral_indicator measurableSet_Icc]
      have hφ1 : φ1 r = min (ENNReal.ofReal (a * |r| ^ n)) (ENNReal.ofReal (c / |r|)) :=
        indicator_of_mem (show r ∈ Icc (-ε) ε from abs_le.mp hrε) _
      rw [hφ1]
      refine le_min ?_ ?_
      · calc ENNReal.ofReal (|r| ^ n) * ∫⁻ q in Icc (-1 : Fin n → ℝ) 1, min (ENNReal.ofReal T)
              (ENNReal.ofReal (s * |r|⁻¹ ^ (n + 1)) * h r q)
            ≤ ENNReal.ofReal (|r| ^ n) * ∫⁻ _ in Icc (-1 : Fin n → ℝ) 1, ENNReal.ofReal T := by
              gcongr with q; exact min_le_left _ _
          _ = ENNReal.ofReal (a * |r| ^ n) := by
              rw [setLIntegral_const, Real.volume_Icc_pi]
              simp only [Pi.one_apply, Pi.neg_apply, sub_neg_eq_add, Finset.prod_const,
                Finset.card_univ, Fintype.card_fin]
              rw [show (1 : ℝ) + 1 = 2 by norm_num, ← ENNReal.ofReal_pow (by norm_num),
                ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [ha_def]; ring
      · calc ENNReal.ofReal (|r| ^ n) * ∫⁻ q in Icc (-1 : Fin n → ℝ) 1, min (ENNReal.ofReal T)
              (ENNReal.ofReal (s * |r|⁻¹ ^ (n + 1)) * h r q)
            ≤ ENNReal.ofReal (|r| ^ n) * ∫⁻ q in Icc (-1 : Fin n → ℝ) 1,
                ENNReal.ofReal (s * |r|⁻¹ ^ (n + 1)) * h r q := by
              gcongr with q; exact min_le_right _ _
          _ ≤ ENNReal.ofReal (|r| ^ n) * (ENNReal.ofReal (s * |r|⁻¹ ^ (n + 1)) *
                ENNReal.ofReal H) := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              gcongr
              exact hH r hr hrε
          _ = ENNReal.ofReal (c / |r|) := by
              rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [hc_def, inv_pow, pow_succ]
              field_simp
    · have : ∀ p, (pivotCone n ε).indicator g (r, p) = 0 := fun p =>
        indicator_of_notMem (fun h' => hrε h'.1) _
      simp only [this, lintegral_zero]; exact zero_le
  have hne : ∀ᵐ r : ℝ ∂volume, r ≠ 0 := Measure.ae_ne volume 0
  calc ∫⁻ x in pivotCone n ε, g x
      = ∫⁻ x, (pivotCone n ε).indicator g x := (lintegral_indicator
          (measurableSet_pivotCone n ε) g).symm
    _ = ∫⁻ r, ∫⁻ p, (pivotCone n ε).indicator g (r, p) := by
        rw [Measure.volume_eq_prod, lintegral_prod _
          (hgm.indicator (measurableSet_pivotCone n ε)).aemeasurable]
    _ ≤ ∫⁻ r, φ1 r := lintegral_mono_ae (hne.mono fun r hr => hfib r hr)
    _ ≤ ENNReal.ofReal (2 * c * (1 + Real.posLog ε + Real.posLog (a / c))) :=
        lintegral_min_pow_div_le n ha hc hε
    _ ≤ ENNReal.ofReal (s * (2 * H * (1 + Real.posLog ε + Real.posLog (2 ^ n * T / H)) +
          2 * H * Real.posLog s⁻¹)) := by
        apply ENNReal.ofReal_le_ofReal
        have e : a / c = (2 ^ n * T / H) * s⁻¹ := by rw [ha_def, hc_def]; field_simp
        have h1 : Real.posLog (a / c) ≤ Real.posLog (2 ^ n * T / H) + Real.posLog s⁻¹ := by
          rw [e]; exact Real.posLog_mul
        have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * c)
        rw [hc_def] at h2 ⊢
        nlinarith

end SLT.Template
