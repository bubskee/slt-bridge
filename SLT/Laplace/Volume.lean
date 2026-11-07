/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Laplace.Integral

/-!
# Volume ⇔ Laplace

The layer-cake identity `Z(N) = ∫_0^∞ e^{-s} V(s/N) ds`, and the transfer between sublevel-volume
bounds `V(t) ≍ t^λ (log 1/t)^{m-1}` (as `t → 0`) and Laplace bounds `Z(N) ≍ N^{-λ} (log N)^{m-1}`
(as `N → ∞`):

* `laplaceLower_of_volume`: a local lower volume bound gives the Laplace lower bound;
* `laplaceUpper_of_volume`: a global upper volume bound gives the Laplace upper bound;
* `laplaceUpper_iff_volume`: for finite `ν`, the Laplace upper bound is *equivalent* to a local upper
  volume bound (`V(1/N) ≤ e Z(N)` gives the converse).

The lower-direction converse (Laplace ⇒ volume, a Tauberian statement) is not here.
Ported from `vector-slt-lean` (`VectorSLT/SLT/Laplace.lean`, b21c0ad) and restated for `rate`.
-/

@[expose] public section

namespace SLT

open MeasureTheory Filter Real Set
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {ν : Measure α} {K : α → ℝ} {lam : ℝ} {m : ℕ}

/-- **Volume ⇒ Laplace (lower).** If `V(t) ≥ c t^λ (log 1/t)^{m-1}` for `0 < t ≤ t₀`, then
`Z(N) ≥ e^{-1} c · rate λ m N` for `N ≥ 1/t₀`. -/
theorem laplaceLower_of_volume (hK : Measurable K) {c t₀ : ℝ} (hc : 0 < c) (ht₀ : 0 < t₀)
    (hV : ∀ t, 0 < t → t ≤ t₀ →
      ENNReal.ofReal (c * t ^ lam * Real.log (1 / t) ^ (m - 1)) ≤ V ν K t) :
    LaplaceLower (Z ν K) lam m := by
  refine ⟨Real.exp (-1) * c, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop t₀⁻¹] with N hNt
  have hN : 0 < N := lt_of_lt_of_le (inv_pos.mpr ht₀) hNt
  have ht : N⁻¹ ≤ t₀ := by rw [inv_le_comm₀ hN ht₀]; exact hNt
  have h1 := hV N⁻¹ (inv_pos.mpr hN) ht
  rw [one_div, inv_inv, Real.inv_rpow hN.le, ← Real.rpow_neg hN.le] at h1
  refine le_trans ?_ (Z_ge_V hK hN)
  have e : Real.exp (-1) * c * rate lam m N =
      Real.exp (-1) * (c * N ^ (-lam) * Real.log N ^ (m - 1)) := by unfold rate; ring
  rw [e, ENNReal.ofReal_mul (Real.exp_pos _).le]
  gcongr
/-! ### The layer-cake identity -/

/-- `∫_{(0,∞)} 1{a ≤ s} e^{-s} ds = e^{-a}` for `a ≥ 0`. -/
theorem lintegral_Ioi_indicator_exp {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ s in Ioi 0, (Ici a).indicator (fun s => ENNReal.ofReal (Real.exp (-s))) s =
      ENNReal.ofReal (Real.exp (-a)) := by
  rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have hset : (Ici a ∩ Ioi 0 : Set ℝ) =ᵐ[volume] Ioi a := by
    rcases eq_or_lt_of_le ha with h | h
    · subst h
      have e : (Ici 0 ∩ Ioi 0 : Set ℝ) = Ioi 0 := inter_eq_right.mpr Ioi_subset_Ici_self
      rw [e]
    · have e : (Ici a ∩ Ioi 0 : Set ℝ) = Ici a :=
        inter_eq_left.mpr (fun x (hx : a ≤ x) => show (0:ℝ) < x from lt_of_lt_of_le h hx)
      rw [e]; exact Ioi_ae_eq_Ici.symm
  rw [setLIntegral_congr hset, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_exp_neg_Ioi]
  · exact (exp_neg_integrableOn_Ioi a one_pos).congr_fun (fun x _ => by simp) measurableSet_Ioi
  · exact Eventually.of_forall fun x => (Real.exp_pos _).le

/-- **Layer cake**: for a nonnegative measurable loss and `N > 0`,
`Z(N) = ∫_0^∞ e^{-s} V(s/N) ds`, i.e. `∫_0^∞ N e^{-Nt} V(t) dt` after `s = Nt`. -/
theorem Z_eq_layercake {ν : Measure α} [SFinite ν] {K : α → ℝ} (hK : Measurable K)
    (hK0 : ∀ x, 0 ≤ K x) {N : ℝ} (hN : 0 < N) :
    Z ν K N = ∫⁻ s in Ioi 0, ENNReal.ofReal (Real.exp (-s)) * V ν K (s / N) := by
  set F : α → ℝ → ENNReal := fun x s =>
    {p : α × ℝ | N * K p.1 ≤ p.2}.indicator (fun p => ENNReal.ofReal (Real.exp (-p.2))) (x, s)
  have hF : Measurable (Function.uncurry F) := by
    refine Measurable.indicator (by fun_prop) ?_
    exact measurableSet_le (by fun_prop) measurable_snd
  have h1 : ∀ x, ENNReal.ofReal (Real.exp (-(N * K x))) = ∫⁻ s in Ioi 0, F x s := by
    intro x
    rw [← lintegral_Ioi_indicator_exp (mul_nonneg hN.le (hK0 x))]
    rfl
  unfold Z
  simp_rw [h1]
  rw [lintegral_lintegral_swap hF.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
  have : (fun x => F x s) = {x | K x ≤ s / N}.indicator
      (fun _ => ENNReal.ofReal (Real.exp (-s))) := by
    funext x
    simp only [F, Set.indicator, mem_ofPred_eq]
    congr 1
    rw [le_div_iff₀ hN, mul_comm]
  rw [this, lintegral_indicator_const (measurableSet_le hK measurable_const)]
  rfl

/-! ### Volume ⇒ Laplace, upper direction -/

/-- The constant `I(λ,k) = ∫_0^∞ e^{-s} s^λ (1 + |log s|)^k ds`. -/
noncomputable def gammaLog (lam : ℝ) (k : ℕ) : ENNReal :=
  ∫⁻ s in Ioi 0, ENNReal.ofReal (Real.exp (-s) * s ^ lam * (1 + |Real.log s|) ^ k)

theorem one_add_abs_log_le {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    1 + |Real.log s| ≤ (1 + 1 / δ) * (s ^ δ + s ^ (-δ)) := by
  have h1 : 0 < s ^ δ := Real.rpow_pos_of_pos hs δ
  have h2 : 0 < s ^ (-δ) := Real.rpow_pos_of_pos hs (-δ)
  rcases le_total 1 s with hs1 | hs1
  · have hl : 0 ≤ Real.log s := Real.log_nonneg hs1
    have hlog := Real.log_le_rpow_div hs.le hδ
    have : 1 ≤ s ^ δ := Real.one_le_rpow hs1 hδ.le
    rw [abs_of_nonneg hl]
    have e : (1 + 1 / δ) * (s ^ δ + s ^ (-δ)) = s ^ δ + s ^ δ / δ + (1 + 1 / δ) * s ^ (-δ) := by
      ring
    rw [e]
    have : 0 ≤ (1 + 1 / δ) * s ^ (-δ) := by positivity
    linarith
  · have hl : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1
    have hlog := Real.log_le_rpow_div (inv_pos.mpr hs).le hδ
    rw [Real.log_inv, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le] at hlog
    have : 1 ≤ s ^ (-δ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs hs1 (by linarith)
    rw [abs_of_nonpos hl]
    have e : (1 + 1 / δ) * (s ^ δ + s ^ (-δ)) = s ^ (-δ) + s ^ (-δ) / δ + (1 + 1 / δ) * s ^ δ := by
      ring
    rw [e]
    have : 0 ≤ (1 + 1 / δ) * s ^ δ := by positivity
    linarith

theorem add_pow_le_two_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    (a + b) ^ k ≤ 2 ^ k * (a ^ k + b ^ k) := by
  have hm : a + b ≤ 2 * max a b := by
    have := le_max_left a b; have := le_max_right a b; linarith
  calc (a + b) ^ k ≤ (2 * max a b) ^ k := pow_le_pow_left₀ (by positivity) hm k
    _ = 2 ^ k * max a b ^ k := mul_pow _ _ _
    _ ≤ 2 ^ k * (a ^ k + b ^ k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rcases le_total a b with h | h
        · rw [max_eq_right h]; have := pow_nonneg ha k; linarith
        · rw [max_eq_left h]; have := pow_nonneg hb k; linarith

theorem gammaLog_lt_top {lam : ℝ} (hlam : 0 < lam) (k : ℕ) : gammaLog lam k < ⊤ := by
  set δ := lam / (2 * (k + 1))
  have hδ : 0 < δ := by positivity
  have hkδ : (k : ℝ) * δ ≤ lam / 2 := by
    simp only [δ]; rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set B := (1 + 1 / δ) ^ k * 2 ^ k
  have hB : 0 ≤ B := by positivity
  set g : ℝ → ℝ := fun s => B * (Real.exp (-s) * s ^ (lam + k * δ + 1 - 1) +
    Real.exp (-s) * s ^ (lam - k * δ + 1 - 1))
  have hg : IntegrableOn g (Ioi 0) :=
    ((Real.GammaIntegral_convergent (by positivity)).add
      (Real.GammaIntegral_convergent (by linarith))).const_mul B
  have hpt : ∀ s ∈ Ioi (0 : ℝ), Real.exp (-s) * s ^ lam * (1 + |Real.log s|) ^ k ≤ g s := by
    intro s hs
    have hs : 0 < s := hs
    have h1 := one_add_abs_log_le hs hδ
    have h2 : (1 + |Real.log s|) ^ k ≤ (1 + 1 / δ) ^ k * (s ^ δ + s ^ (-δ)) ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 k
    have h3 := add_pow_le_two_pow (Real.rpow_pos_of_pos hs δ).le
      (Real.rpow_pos_of_pos hs (-δ)).le k
    have e1 : (s ^ δ) ^ k = s ^ ((k : ℝ) * δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le, mul_comm]
    have e2 : (s ^ (-δ)) ^ k = s ^ (-((k : ℝ) * δ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]; ring_nf
    rw [e1, e2] at h3
    have e3 : s ^ lam * s ^ ((k : ℝ) * δ) = s ^ (lam + k * δ + 1 - 1) := by
      rw [← Real.rpow_add hs]; ring_nf
    have e4 : s ^ lam * s ^ (-((k : ℝ) * δ)) = s ^ (lam - k * δ + 1 - 1) := by
      rw [← Real.rpow_add hs]; ring_nf
    have hE : 0 ≤ Real.exp (-s) * s ^ lam := by positivity
    calc Real.exp (-s) * s ^ lam * (1 + |Real.log s|) ^ k
        ≤ Real.exp (-s) * s ^ lam * ((1 + 1 / δ) ^ k * (2 ^ k * (s ^ ((k : ℝ) * δ) +
            s ^ (-((k : ℝ) * δ))))) :=
          mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))) hE
      _ = g s := by
          simp only [g, B]; rw [← e3, ← e4]; ring
  calc gammaLog lam k ≤ ∫⁻ s in Ioi 0, ENNReal.ofReal (g s) := by
        apply setLIntegral_mono (by fun_prop)
        intro s hs; exact ENNReal.ofReal_le_ofReal (hpt s hs)
    _ < ⊤ := hg.lintegral_lt_top

/-- **Volume ⇒ Laplace (upper), explicit form.** If `V(t) ≤ C t^λ (1+|log t|)^k` for all
`t > 0`, then `Z(N) ≤ C N^{-λ} (1 + log N)^k · I(λ,k)` for `N ≥ 1`. -/
theorem Z_le_of_volume {ν : Measure α} [SFinite ν] {K : α → ℝ} (hK : Measurable K)
    (hK0 : ∀ x, 0 ≤ K x) {C lam : ℝ} {k : ℕ} (hC : 0 ≤ C)
    (hV : ∀ t, 0 < t → V ν K t ≤ ENNReal.ofReal (C * t ^ lam * (1 + |Real.log t|) ^ k))
    {N : ℝ} (hN : 1 ≤ N) :
    Z ν K N ≤ ENNReal.ofReal (C * N ^ (-lam) * (1 + Real.log N) ^ k) * gammaLog lam k := by
  have hN0 : 0 < N := by linarith
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN
  rw [Z_eq_layercake hK hK0 hN0, gammaLog, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Ioi
  intro s hs
  have hs : 0 < s := hs
  calc ENNReal.ofReal (Real.exp (-s)) * V ν K (s / N)
      ≤ ENNReal.ofReal (Real.exp (-s)) *
          ENNReal.ofReal (C * (s / N) ^ lam * (1 + |Real.log (s / N)|) ^ k) := by
        gcongr; exact hV (s / N) (div_pos hs hN0)
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hp : (s / N) ^ lam = s ^ lam * N ^ (-lam) := by
        rw [Real.div_rpow hs.le hN0.le, Real.rpow_neg hN0.le, div_eq_mul_inv]
      have hlog : 1 + |Real.log (s / N)| ≤ (1 + |Real.log s|) * (1 + Real.log N) := by
        rw [Real.log_div hs.ne' hN0.ne']
        have := abs_sub (Real.log s) (Real.log N)
        rw [abs_of_nonneg hlN] at this
        nlinarith [abs_nonneg (Real.log s)]
      have hlogk : (1 + |Real.log (s / N)|) ^ k ≤
          (1 + |Real.log s|) ^ k * (1 + Real.log N) ^ k := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hlog k
      rw [hp]
      have hA : 0 ≤ Real.exp (-s) * (C * (s ^ lam * N ^ (-lam))) := by positivity
      calc Real.exp (-s) * (C * (s ^ lam * N ^ (-lam)) * (1 + |Real.log (s / N)|) ^ k)
          = Real.exp (-s) * (C * (s ^ lam * N ^ (-lam))) * (1 + |Real.log (s / N)|) ^ k := by
            ring
        _ ≤ Real.exp (-s) * (C * (s ^ lam * N ^ (-lam))) *
            ((1 + |Real.log s|) ^ k * (1 + Real.log N) ^ k) := mul_le_mul_of_nonneg_left hlogk hA
        _ = C * N ^ (-lam) * (1 + Real.log N) ^ k *
            (Real.exp (-s) * s ^ lam * (1 + |Real.log s|) ^ k) := by ring

/-- **Volume ⇒ Laplace (upper).** A global sublevel bound `V(t) ≤ C t^λ (1+|log t|)^{m-1}`
with `λ > 0` gives `Z(N) ≤ C' · rate λ m N` for large `N`. -/
theorem laplaceUpper_of_volume [SFinite ν] (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {C : ℝ}
    (hC : 0 ≤ C) (hlam : 0 < lam)
    (hV : ∀ t, 0 < t → V ν K t ≤ ENNReal.ofReal (C * t ^ lam * (1 + |Real.log t|) ^ (m - 1))) :
    LaplaceUpper (Z ν K) lam m := by
  set I := gammaLog lam (m - 1)
  have hI := gammaLog_lt_top hlam (m - 1)
  refine ⟨C * 2 ^ (m - 1) * I.toReal, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
  have hN1 : 1 ≤ N := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hN
  have hlN : 1 ≤ Real.log N := one_le_log_of_exp_le hN
  refine (Z_le_of_volume hK hK0 hC hV hN1).trans ?_
  rw [← ENNReal.ofReal_toReal hI.ne, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h2 : (1 + Real.log N) ^ (m - 1) ≤ 2 ^ (m - 1) * Real.log N ^ (m - 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hA : 0 ≤ C * N ^ (-lam) := by positivity
  have hI0 : 0 ≤ I.toReal := ENNReal.toReal_nonneg
  calc C * N ^ (-lam) * (1 + Real.log N) ^ (m - 1) * I.toReal
      ≤ C * N ^ (-lam) * (2 ^ (m - 1) * Real.log N ^ (m - 1)) * I.toReal := by gcongr
    _ = _ := by unfold rate; ring

/-- For a finite measure, a *local* upper volume bound `V(t) ≤ C t^λ (log 1/t)^{m-1}` on `(0, t₀]`
extends to a global one of the form used by `laplaceUpper_of_volume`. -/
theorem volume_global_of_local [IsFiniteMeasure ν] {C t₀ : ℝ} (ht₀ : 0 < t₀) (hlam : 0 < lam)
    (hV : ∀ t, 0 < t → t ≤ t₀ →
      V ν K t ≤ ENNReal.ofReal (C * t ^ lam * Real.log (1 / t) ^ (m - 1))) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t, 0 < t →
      V ν K t ≤ ENNReal.ofReal (C' * t ^ lam * (1 + |Real.log t|) ^ (m - 1)) := by
  set s := min t₀ 1 with hs
  have hs0 : 0 < s := lt_min ht₀ one_pos
  set B := (ν univ).toReal
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  refine ⟨max C 0 + B / s ^ lam, by positivity, fun t ht => ?_⟩
  have hk1 : 1 ≤ (1 + |Real.log t|) ^ (m - 1) := one_le_pow₀ (by linarith [abs_nonneg (Real.log t)])
  have htl : 0 < t ^ lam := Real.rpow_pos_of_pos ht lam
  rcases le_or_gt t s with hts | hts
  · refine (hV t ht (hts.trans (min_le_left _ _))).trans (ENNReal.ofReal_le_ofReal ?_)
    have ht1 : t ≤ 1 := hts.trans (min_le_right _ _)
    have hl : Real.log (1 / t) = |Real.log t| := by
      rw [one_div, Real.log_inv, abs_of_nonpos (Real.log_nonpos ht.le ht1)]
    have hl0 : 0 ≤ |Real.log t| := abs_nonneg _
    rw [hl]
    calc C * t ^ lam * |Real.log t| ^ (m - 1) ≤ max C 0 * t ^ lam * |Real.log t| ^ (m - 1) := by
          gcongr; exact le_max_left _ _
      _ ≤ max C 0 * t ^ lam * (1 + |Real.log t|) ^ (m - 1) := by
          gcongr; linarith
      _ ≤ (max C 0 + B / s ^ lam) * t ^ lam * (1 + |Real.log t|) ^ (m - 1) := by
          gcongr; linarith [show 0 ≤ B / s ^ lam by positivity]
  · have hst : s ^ lam ≤ t ^ lam := Real.rpow_le_rpow hs0.le hts.le hlam.le
    have hsl : 0 < s ^ lam := Real.rpow_pos_of_pos hs0 lam
    calc V ν K t ≤ ν univ := measure_mono (subset_univ _)
      _ = ENNReal.ofReal B := (ENNReal.ofReal_toReal (measure_ne_top ν univ)).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : B ≤ B / s ^ lam * t ^ lam := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hsl]; exact mul_le_mul_of_nonneg_left hst hB
        calc B ≤ B / s ^ lam * t ^ lam := h1
          _ ≤ B / s ^ lam * t ^ lam * (1 + |Real.log t|) ^ (m - 1) := le_mul_of_one_le_right
              (by positivity) hk1
          _ ≤ _ := by gcongr; linarith [le_max_right C 0]

/-- **Laplace ⇒ volume (upper).** An eventual upper bound `Z(N) ≤ C · rate λ m N` gives
`V(t) ≤ e C t^λ (log 1/t)^{m-1}` for small `t > 0`. -/
theorem volume_le_of_laplaceUpper (hK : Measurable K) (h : LaplaceUpper (Z ν K) lam m) :
    ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t, 0 < t → t ≤ t₀ →
      V ν K t ≤ ENNReal.ofReal (C * t ^ lam * Real.log (1 / t) ^ (m - 1)) := by
  obtain ⟨C, hC, h⟩ := h.exists_pos
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
  have hN1 : 0 < max N₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨Real.exp 1 * C, (max N₀ 1)⁻¹, inv_pos.mpr hN1, fun t ht htle => ?_⟩
  have hN : max N₀ 1 ≤ t⁻¹ := by rw [le_inv_comm₀ hN1 ht]; exact htle
  have hZ := hN₀ t⁻¹ ((le_max_left _ _).trans hN)
  have hV := V_le_Z (ν := ν) hK (inv_pos.mpr ht)
  rw [inv_inv] at hV
  refine hV.trans ?_
  calc ENNReal.ofReal (Real.exp 1) * Z ν K t⁻¹
      ≤ ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (C * rate lam m t⁻¹) := by gcongr
    _ = ENNReal.ofReal (Real.exp 1 * (C * rate lam m t⁻¹)) :=
        (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
    _ = _ := by
        congr 1; unfold rate
        rw [Real.rpow_neg (inv_nonneg.mpr ht.le), Real.inv_rpow ht.le, inv_inv, one_div]; ring

/-- **Upper Laplace bound ⇔ local upper volume bound**, for a finite measure, `K ≥ 0`, `λ > 0`. -/
theorem laplaceUpper_iff_volume [IsFiniteMeasure ν] (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
    (hlam : 0 < lam) :
    LaplaceUpper (Z ν K) lam m ↔ ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t, 0 < t → t ≤ t₀ →
      V ν K t ≤ ENNReal.ofReal (C * t ^ lam * Real.log (1 / t) ^ (m - 1)) := by
  refine ⟨volume_le_of_laplaceUpper hK, fun ⟨C, t₀, ht₀, hV⟩ => ?_⟩
  obtain ⟨C', hC', hV'⟩ := volume_global_of_local ht₀ hlam hV
  exact laplaceUpper_of_volume hK hK0 hC' hlam hV'

end SLT
