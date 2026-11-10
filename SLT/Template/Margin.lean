/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Template.Fibre
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# The margin template (brief 03, T2)

cubic-chaos proves its log-free pairs (Theorems E, K, N and the invertible cases) with one
template:

1. **regular active coordinates**: `K ≍ |u|² + ‖g(w)‖²`, where `u ∈ ℝᵃ` are `a` coordinates in
   which the loss is non-degenerate;
2. **weighted homogeneity**: `g(r ξ) = r^d 𝒢(r, ξ)` with `𝒢(0, ·) = R`, the leading map;
3. **a strict angular margin**: `‖𝒢(r, ·)‖^{-2s}` is integrable over angles, uniformly in small `r`,
   for some `s` with `2 d s > D = dim w`;
4. **the radial split** (cubic-chaos (K24)): then `∫ e^{-N ‖g‖²} ≲ N^{-D/(2d)}`, with **no
   logarithm**, because the margin is strict.

Items 1, 2 and 4 are elementary. Item 3 is where resolution of singularities and holomorphic
stability enter. In the paper it comes from three ingredients:
* a complex threshold `lct(R) > D/d` at the nonzero zeros of the leading map;
* Phong–Sturm stability in the radial parameter;
* Bierstone–Milman real transfer.

Here item 3 is the **named hypothesis** `AngularMargin`, stated in Mathlib-only real vocabulary.
The project plan (kept outside this repository) records what a future `hironaka` import would
discharge. Everything else is
proved:
* `lintegral_eq_shell_average`: polar-free radial coordinates, by averaging over dyadic shells;
* `lintegral_exp_le_of_angularMargin`: the radial split, with an explicit constant;
* `lintegral_exp_neg_sum_sq`: the Gaussian factor of the active coordinates;
* `laplaceUpper_of_angularMargin`, `hasLaplacePair_of_angularMargin`: the template, giving the upper
  rate `(a/2 + D/(2d), 1)`, and with a lower-bound core the pair `(a/2 + D/(2d), 1)`.

Norms on `Fin D → ℝ` are the sup norm, and the shell is `{1/2 ≤ ‖ξ‖ < 1}`.
-/

@[expose] public section

namespace SLT.Template

open MeasureTheory Set Real Filter Metric
open scoped ENNReal

/-! ### Shells and radial averaging -/

/-- The unit shell `{ξ | 1/2 ≤ ‖ξ‖ < 1}` in `ℝᴰ` (sup norm). -/
def shell (D : ℕ) : Set (Fin D → ℝ) := {ξ | 1 / 2 ≤ ‖ξ‖ ∧ ‖ξ‖ < 1}

/-- The shell is measurable. -/
theorem measurableSet_shell (D : ℕ) : MeasurableSet (shell D) :=
  (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

/-- The shell has volume at most `2ᴰ`. -/
theorem volume_shell_le (D : ℕ) : volume (shell D) ≤ ENNReal.ofReal (2 ^ D) := by
  calc volume (shell D) ≤ volume (closedBall (0 : Fin D → ℝ) 1) :=
        measure_mono fun ξ hξ => mem_closedBall_zero_iff.mpr hξ.2.le
    _ = ENNReal.ofReal (2 ^ D) := by
        rw [Real.volume_pi_closedBall 0 zero_le_one, Fintype.card_fin, mul_one]

/-- **Radial averaging over dyadic shells**: for `D ≥ 1` and measurable `f ≥ 0`,
`log 2 · ∫ f = ∫_{r > 0} r^{D-1} ∫_{shell} f(r ξ) dξ dr`. Each `w ≠ 0` lies in `r • shell` exactly
for `r ∈ (‖w‖, 2‖w‖]`, a set of `dr/r`-measure `log 2`. -/
theorem lintegral_eq_shell_average {D : ℕ} (hD : 1 ≤ D) {f : (Fin D → ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (D - 1)) * ∫⁻ ξ in shell D, f (r • ξ) =
      ENNReal.ofReal (Real.log 2) * ∫⁻ w, f w := by
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  set E : Set (ℝ × (Fin D → ℝ)) := {p | 0 < p.1 ∧ p.1 / 2 ≤ ‖p.2‖ ∧ ‖p.2‖ < p.1} with hE
  have hEm : MeasurableSet E :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_le (f := fun p : ℝ × (Fin D → ℝ) => p.1 / 2) (g := fun p => ‖p.2‖)
        (by fun_prop) (by fun_prop)).inter
        (measurableSet_lt (f := fun p : ℝ × (Fin D → ℝ) => ‖p.2‖) (g := fun p => p.1)
          (by fun_prop) measurable_fst))
  set Φ : ℝ × (Fin D → ℝ) → ℝ≥0∞ := E.indicator fun p => ENNReal.ofReal (1 / p.1) * f p.2
  have hΦ : Measurable Φ :=
    ((by fun_prop : Measurable fun p : ℝ × (Fin D → ℝ) => ENNReal.ofReal (1 / p.1)).mul
      (hf.comp measurable_snd)).indicator hEm
  -- the `r`-side
  have hr : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal (r ^ (D - 1)) * ∫⁻ ξ in shell D, f (r • ξ) =
      ∫⁻ w, Φ (r, w) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr
    have hmr : Measurable fun w => Φ (r, w) := hΦ.comp measurable_prodMk_left
    rw [lintegral_eq_smul_rescale hmr hr0.ne', abs_of_pos hr0]
    have hpt : ∀ q : Fin D → ℝ, Φ (r, r • q) =
        ENNReal.ofReal (1 / r) * (shell D).indicator (fun q => f (r • q)) q := by
      intro q
      have hn : ‖r • q‖ = r * ‖q‖ := by rw [norm_smul, Real.norm_of_nonneg hr0.le]
      by_cases hq : q ∈ shell D
      · have : (r, r • q) ∈ E := ⟨hr0, by rw [hn]; nlinarith [hq.1], by rw [hn]; nlinarith [hq.2]⟩
        simp only [Φ]; rw [indicator_of_mem this, indicator_of_mem hq]
      · have : (r, r • q) ∉ E := by
          rintro ⟨-, h1, h2⟩
          rw [hn] at h1 h2
          exact hq ⟨by nlinarith, by nlinarith⟩
        simp only [Φ]; rw [indicator_of_notMem this, indicator_of_notMem hq, mul_zero]
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator (measurableSet_shell D),
      ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [pow_sub₀ _ hr0.ne' hD, pow_one]; field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi hr]
  -- swap and do the `r`-integral
  have hΦ0 : ∀ w r, r ∉ Ioi (0 : ℝ) → Φ (r, w) = 0 := fun w r hr =>
    indicator_of_notMem (fun h => hr h.1) _
  calc ∫⁻ r in Ioi (0 : ℝ), ∫⁻ w, Φ (r, w)
      = ∫⁻ r, ∫⁻ w, Φ (r, w) := by
        rw [← lintegral_indicator measurableSet_Ioi]
        refine lintegral_congr fun r => ?_
        by_cases hr : r ∈ Ioi (0 : ℝ)
        · rw [indicator_of_mem hr]
        · rw [indicator_of_notMem hr]; simp [hΦ0 _ r hr]
    _ = ∫⁻ w, ∫⁻ r, Φ (r, w) := lintegral_lintegral_swap hΦ.aemeasurable
    _ = ∫⁻ w, ENNReal.ofReal (Real.log 2) * f w := by
        refine lintegral_congr_ae ?_
        filter_upwards [Measure.ae_ne volume (0 : Fin D → ℝ)] with w hw
        have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
        have hsec : (fun r => Φ (r, w)) =
            (Ioc ‖w‖ (2 * ‖w‖)).indicator fun r => ENNReal.ofReal (1 / r) * f w := by
          funext r
          simp only [Φ, hE, indicator, mem_ofPred_eq, mem_Ioc]
          congr 1
          refine propext ⟨fun ⟨h0, h1, h2⟩ => ⟨h2, by linarith⟩, fun ⟨h1, h2⟩ => ⟨by linarith,
            by linarith, h1⟩⟩
        rw [hsec, lintegral_indicator measurableSet_Ioc, lintegral_mul_const _ (by fun_prop),
          lintegral_Ioc_div hw0 (by linarith) zero_le_one, one_mul,
          mul_div_cancel_right₀ _ hw0.ne', mul_comm]
    _ = ENNReal.ofReal (Real.log 2) * ∫⁻ w, f w := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-! ### Two elementary estimates -/

/-- `e^{-y} ≤ s^s y^{-s}` for `y, s > 0`. -/
theorem exp_neg_le_rpow {y s : ℝ} (hy : 0 < y) (hs : 0 < s) :
    Real.exp (-y) ≤ s ^ s * y ^ (-s) := by
  have key : s * Real.log y - y ≤ s * Real.log s := by
    have h := Real.log_le_sub_one_of_pos (div_pos hy hs)
    rw [Real.log_div hy.ne' hs.ne'] at h
    have := mul_le_mul_of_nonneg_left h hs.le
    have e : s * (y / s - 1) = y - s := by field_simp
    nlinarith [Real.add_one_le_exp (-s)]
  have h1 : Real.exp (-y) * y ^ s ≤ s ^ s := by
    rw [Real.rpow_def_of_pos hy, Real.rpow_def_of_pos hs, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  rw [Real.rpow_neg hy.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hy s)]
  exact h1

/-- The radial integral `∫_{r>0} r^{D-1} min (V, B r^{-p}) dr ≤ V ρᴰ/D + B ρ^{D-p}/(p-D)` for any
`ρ > 0`, when `p > D ≥ 1`. -/
theorem lintegral_radial_min_le {D : ℕ} (hD : 1 ≤ D) {V B p ρ : ℝ} (hV : 0 ≤ V) (hB : 0 ≤ B)
    (hp : (D : ℝ) < p) (hρ : 0 < ρ) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (D - 1)) *
        min (ENNReal.ofReal V) (ENNReal.ofReal (B * r ^ (-p))) ≤
      ENNReal.ofReal (V * ρ ^ D / D + B * ρ ^ ((D : ℝ) - p) / (p - D)) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hsplit : Ioi (0 : ℝ) = Ioc 0 ρ ∪ Ioi ρ := (Ioc_union_Ioi_eq_Ioi hρ.le).symm
  rw [hsplit]
  refine (lintegral_union_le _ _ _).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (div_nonneg (by positivity) (by linarith))]
  gcongr
  · -- near zero: `V ∫_0^ρ r^{D-1}`
    calc ∫⁻ r in Ioc 0 ρ, ENNReal.ofReal (r ^ (D - 1)) *
          min (ENNReal.ofReal V) (ENNReal.ofReal (B * r ^ (-p)))
        ≤ ∫⁻ r in Ioc 0 ρ, ENNReal.ofReal (V * r ^ (D - 1)) := by
          refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
          rw [mul_comm V, ENNReal.ofReal_mul (pow_nonneg hr.1.le _)]
          exact mul_le_mul' le_rfl (min_le_left _ _)
      _ = ENNReal.ofReal (∫ r in Ioc 0 ρ, V * r ^ (D - 1)) := by
          rw [ofReal_integral_eq_lintegral_ofReal]
          · exact (continuous_const.mul (continuous_pow _)).integrableOn_Icc.mono_set
              Ioc_subset_Icc_self
          · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
            exact mul_nonneg hV (pow_nonneg hr.1.le _)
      _ = ENNReal.ofReal (V * ρ ^ D / D) := by
          rw [← intervalIntegral.integral_of_le hρ.le, intervalIntegral.integral_const_mul,
            integral_pow]
          congr 1
          rw [Nat.sub_add_cancel hD, zero_pow (by omega), sub_zero, Nat.cast_sub hD,
            Nat.cast_one, sub_add_cancel]
          ring
  · -- away from zero: `B ∫_ρ^∞ r^{D-1-p}`
    have hq : (D : ℝ) - 1 - p < -1 := by linarith
    have hpt : ∀ r ∈ Ioi ρ, ENNReal.ofReal (r ^ (D - 1)) *
        min (ENNReal.ofReal V) (ENNReal.ofReal (B * r ^ (-p))) ≤
        ENNReal.ofReal (B * r ^ ((D : ℝ) - 1 - p)) := by
      intro r hr
      have hr0 : 0 < r := hρ.trans hr
      refine (mul_le_mul' le_rfl (min_le_right _ _)).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_mul (pow_nonneg hr0.le _)]
      congr 1
      rw [show (D : ℝ) - 1 - p = ((D - 1 : ℕ) : ℝ) + -p by rw [Nat.cast_sub hD]; push_cast; ring,
        Real.rpow_add hr0, Real.rpow_natCast]
      ring
    calc _ ≤ ∫⁻ r in Ioi ρ, ENNReal.ofReal (B * r ^ ((D : ℝ) - 1 - p)) :=
          setLIntegral_mono' measurableSet_Ioi hpt
      _ = ENNReal.ofReal (∫ r in Ioi ρ, B * r ^ ((D : ℝ) - 1 - p)) := by
          rw [ofReal_integral_eq_lintegral_ofReal]
          · exact (integrableOn_Ioi_rpow_of_lt hq hρ).const_mul B
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
            exact mul_nonneg hB (Real.rpow_nonneg (hρ.trans hr).le _)
      _ = ENNReal.ofReal (B * ρ ^ ((D : ℝ) - p) / (p - D)) := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt hq hρ]
          congr 1
          rw [show (D : ℝ) - 1 - p + 1 = (D : ℝ) - p by ring]
          have : (D : ℝ) - p ≠ 0 := by linarith
          field_simp
          ring

/-! ### The named hypothesis and the radial split -/

/-- **The angular margin (named hypothesis).** `G` (the squared norm `‖g‖²` of the inactive map) is
weighted homogeneous of degree `2d` near `0`, `G(r ξ) = r^{2d} H(r, ξ)` on the shell for
`0 < r ≤ ε`, and the angular part has a margin `s`: `∫_{shell} H(r, ·)^{-s} ≤ M` uniformly in `r`.
With `2 d s > D` this is the strict margin of cubic-chaos (K4)/(N2). It is the only
non-elementary input of the margin template. The project plan (kept outside this repository)
records how `hironaka` (real transfer)
together with a stability theorem would discharge it from a complex threshold bound. -/
def AngularMargin {D : ℕ} (G : (Fin D → ℝ) → ℝ) (d : ℕ) (s ε M : ℝ) : Prop :=
  ∃ H : ℝ → (Fin D → ℝ) → ℝ,
    (∀ r : ℝ, 0 < r → r ≤ ε → ∀ ξ ∈ shell D, G (r • ξ) = r ^ (2 * d) * H r ξ ∧ 0 ≤ H r ξ) ∧
    ∀ r : ℝ, 0 < r → r ≤ ε → ∫⁻ ξ in shell D, ENNReal.ofReal (H r ξ) ^ (-s) ≤ ENNReal.ofReal M

/-- The constant of the radial split. -/
noncomputable def marginConst (D d : ℕ) (s M : ℝ) : ℝ :=
  (Real.log 2)⁻¹ * (2 ^ D / D + s ^ s * M / (2 * d * s - D))

/-- **The radial split (cubic-chaos (K24)), no logarithm.** Under the angular margin with
`2 d s > D`, `∫_{‖w‖ ≤ ε/2} e^{-N G} ≤ marginConst · N^{-D/(2d)}` for every `N > 0`. -/
theorem lintegral_exp_le_of_angularMargin {D d : ℕ} (hD : 1 ≤ D) (hd : 1 ≤ d)
    {G : (Fin D → ℝ) → ℝ} (hG : Measurable G) {s ε M : ℝ} (hs : 0 < s)
    (hM : 0 ≤ M) (hmargin : (D : ℝ) < 2 * d * s) (hA : AngularMargin G d s ε M) {N : ℝ}
    (hN : 0 < N) :
    ∫⁻ w in closedBall (0 : Fin D → ℝ) (ε / 2), ENNReal.ofReal (Real.exp (-(N * G w))) ≤
      ENNReal.ofReal (marginConst D d s M * N ^ (-((D : ℝ) / (2 * d)))) := by
  obtain ⟨H, hGH, hHint⟩ := hA
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set f : (Fin D → ℝ) → ℝ≥0∞ :=
    (closedBall (0 : Fin D → ℝ) (ε / 2)).indicator fun w => ENNReal.ofReal (Real.exp (-(N * G w)))
  have hf : Measurable f :=
    (by fun_prop : Measurable fun w => ENNReal.ofReal (Real.exp (-(N * G w)))).indicator
      isClosed_closedBall.measurableSet
  set p := 2 * d * s
  set B := s ^ s * N ^ (-s) * M
  have hB : 0 ≤ B := by positivity
  -- the shell bound at radius `r`
  have hsh : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal (r ^ (D - 1)) * ∫⁻ ξ in shell D, f (r • ξ) ≤
      ENNReal.ofReal (r ^ (D - 1)) *
        min (ENNReal.ofReal (2 ^ D)) (ENNReal.ofReal (B * r ^ (-p))) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr
    refine mul_le_mul' le_rfl ?_
    by_cases hrε : r ≤ ε
    · refine le_min ?_ ?_
      · calc ∫⁻ ξ in shell D, f (r • ξ) ≤ ∫⁻ _ in shell D, 1 := by
              refine setLIntegral_mono' (measurableSet_shell D) fun ξ hξ => ?_
              refine (indicator_le_self _ _ _).trans ?_
              obtain ⟨hG', hH0⟩ := hGH r hr0 hrε ξ hξ
              simp only
              rw [hG']
              exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr
                (mul_nonneg hN.le (mul_nonneg (pow_nonneg hr0.le _) hH0))))
          _ ≤ ENNReal.ofReal (2 ^ D) := by rw [setLIntegral_one]; exact volume_shell_le D
      · calc ∫⁻ ξ in shell D, f (r • ξ)
            ≤ ∫⁻ ξ in shell D, ENNReal.ofReal (s ^ s * (N * r ^ (2 * d)) ^ (-s)) *
                ENNReal.ofReal (H r ξ) ^ (-s) := by
              refine setLIntegral_mono' (measurableSet_shell D) fun ξ hξ => ?_
              obtain ⟨hG', hH0⟩ := hGH r hr0 hrε ξ hξ
              simp only [f]
              refine (indicator_le_self _ _ _).trans ?_
              simp only
              rw [hG']
              rcases eq_or_lt_of_le hH0 with h0 | h0
              · rw [← h0, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith),
                  ENNReal.mul_top (by
                    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)]
                exact le_top
              · rw [ENNReal.ofReal_rpow_of_pos h0, ← ENNReal.ofReal_mul (by positivity)]
                apply ENNReal.ofReal_le_ofReal
                have hy : 0 < N * (r ^ (2 * d) * H r ξ) := by positivity
                calc Real.exp (-(N * (r ^ (2 * d) * H r ξ)))
                    ≤ s ^ s * (N * (r ^ (2 * d) * H r ξ)) ^ (-s) := exp_neg_le_rpow hy hs
                  _ = s ^ s * (N * r ^ (2 * d)) ^ (-s) * H r ξ ^ (-s) := by
                      rw [← mul_assoc N, Real.mul_rpow (by positivity) h0.le]; ring
          _ = ENNReal.ofReal (s ^ s * (N * r ^ (2 * d)) ^ (-s)) *
                ∫⁻ ξ in shell D, ENNReal.ofReal (H r ξ) ^ (-s) :=
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ ≤ ENNReal.ofReal (s ^ s * (N * r ^ (2 * d)) ^ (-s)) * ENNReal.ofReal M := by
              gcongr; exact hHint r hr0 hrε
          _ = ENNReal.ofReal (B * r ^ (-p)) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [Real.mul_rpow hN.le (by positivity), ← Real.rpow_natCast,
                ← Real.rpow_mul hr0.le]
              simp only [B, p]; push_cast; ring_nf
    · have : ∀ ξ ∈ shell D, f (r • ξ) = 0 := by
        intro ξ hξ
        refine indicator_of_notMem ?_ _
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hr0.le, not_le]
        nlinarith [hξ.1, not_le.mp hrε]
      rw [setLIntegral_congr_fun (measurableSet_shell D) this, lintegral_zero]
      exact zero_le
  -- assemble
  set ρ := N ^ (-(1 / (2 * (d : ℝ))))
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hN _
  have hmain := lintegral_eq_shell_average hD hf
  have hrad := lintegral_radial_min_le hD (V := 2 ^ D) (B := B) (p := p) (by positivity) hB
    hmargin hρ
  have hle : ENNReal.ofReal (Real.log 2) * ∫⁻ w, f w ≤
      ENNReal.ofReal (2 ^ D * ρ ^ D / D + B * ρ ^ ((D : ℝ) - p) / (p - D)) := by
    rw [← hmain]; exact (setLIntegral_mono' measurableSet_Ioi hsh).trans hrad
  -- the exponents
  have hρD : ρ ^ D = N ^ (-((D : ℝ) / (2 * d))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; congr 1; field_simp
  have hρp : B * ρ ^ ((D : ℝ) - p) = s ^ s * M * N ^ (-((D : ℝ) / (2 * d))) := by
    simp only [B]
    rw [← Real.rpow_mul hN.le]
    have e : -s + (-(1 / (2 * (d : ℝ))) * ((D : ℝ) - p)) = -((D : ℝ) / (2 * d)) := by
      simp only [p]; field_simp; ring
    calc s ^ s * N ^ (-s) * M * N ^ (-(1 / (2 * (d : ℝ))) * ((D : ℝ) - p))
        = s ^ s * M * (N ^ (-s) * N ^ (-(1 / (2 * (d : ℝ))) * ((D : ℝ) - p))) := by ring
      _ = s ^ s * M * N ^ (-((D : ℝ) / (2 * d))) := by rw [← Real.rpow_add hN, e]
  rw [hρD, hρp] at hle
  rw [← lintegral_indicator isClosed_closedBall.measurableSet]
  have hl2' : ENNReal.ofReal (Real.log 2) ≠ 0 := by simpa using hl2
  calc ∫⁻ w, f w = (ENNReal.ofReal (Real.log 2))⁻¹ * (ENNReal.ofReal (Real.log 2) * ∫⁻ w, f w) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hl2' ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal (Real.log 2))⁻¹ * ENNReal.ofReal (2 ^ D * N ^ (-((D : ℝ) / (2 * d))) / D +
          s ^ s * M * N ^ (-((D : ℝ) / (2 * d))) / (p - D)) := by gcongr
    _ = ENNReal.ofReal (marginConst D d s M * N ^ (-((D : ℝ) / (2 * d)))) := by
        rw [← ENNReal.ofReal_inv_of_pos hl2, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [marginConst, p]
        have : (2 * d * s - D) ≠ 0 := by linarith
        field_simp

/-! ### Active coordinates and the template -/

/-- The Gaussian factor of `a` regular active coordinates: `∫ e^{-N Σ uᵢ²} = (π/N)^{a/2}`. -/
theorem lintegral_exp_neg_sum_sq (a : ℕ) {N : ℝ} (hN : 0 < N) :
    ∫⁻ u : Fin a → ℝ, ENNReal.ofReal (Real.exp (-(N * ∑ i, u i ^ 2))) =
      ENNReal.ofReal (√(Real.pi / N) ^ a) := by
  have hint : Integrable (fun u : Fin a → ℝ => Real.exp (-(N * ∑ i, u i ^ 2))) := by
    have e : (fun u : Fin a → ℝ => Real.exp (-(N * ∑ i, u i ^ 2))) =
        fun u => ∏ i, Real.exp (-N * u i ^ 2) := by
      funext u; rw [← Real.exp_sum]; congr 1; rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    exact Integrable.fintype_prod (f := fun _ x => Real.exp (-N * x ^ 2))
      fun _ => integrable_exp_neg_mul_sq hN
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun u => (Real.exp_pos _).le)]
  congr 1
  have e : (fun u : Fin a → ℝ => Real.exp (-(N * ∑ i, u i ^ 2))) =
      fun u => ∏ i, Real.exp (-N * u i ^ 2) := by
    funext u; rw [← Real.exp_sum]; congr 1; rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [e, integral_fintype_prod_volume_eq_prod (f := fun _ x => Real.exp (-N * x ^ 2))]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, integral_gaussian]

/-- The model integral of the margin template: `a` active coordinates with loss `Σ uᵢ²` and the
inactive coordinates on the ball `‖w‖ ≤ ε/2` with loss `G`. -/
noncomputable def marginModel {a D : ℕ} (G : (Fin D → ℝ) → ℝ) (ε N : ℝ) : ℝ≥0∞ :=
  ∫⁻ y : (Fin a → ℝ) × (Fin D → ℝ) in univ ×ˢ closedBall (0 : Fin D → ℝ) (ε / 2),
    ENNReal.ofReal (Real.exp (-(N * (∑ i : Fin a, y.1 i ^ 2 + G y.2))))

/-- **The model integral has upper rate `(a/2 + D/(2d), 1)`.** -/
theorem marginModel_laplaceUpper {a D d : ℕ} (hD : 1 ≤ D) (hd : 1 ≤ d)
    {G : (Fin D → ℝ) → ℝ} (hG : Measurable G) {s ε M : ℝ} (hs : 0 < s)
    (hM : 0 ≤ M) (hmargin : (D : ℝ) < 2 * d * s) (hA : AngularMargin G d s ε M) :
    LaplaceUpper (fun N => marginModel (a := a) G ε N) ((a : ℝ) / 2 + D / (2 * d)) 1 := by
  refine ⟨Real.pi ^ ((a : ℝ) / 2) * marginConst D d s M, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hsplit : marginModel (a := a) G ε N =
      (∫⁻ u : Fin a → ℝ, ENNReal.ofReal (Real.exp (-(N * ∑ i, u i ^ 2)))) *
        ∫⁻ w in closedBall (0 : Fin D → ℝ) (ε / 2), ENNReal.ofReal (Real.exp (-(N * G w))) := by
    unfold marginModel
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
    have hm1 : Measurable fun u : Fin a → ℝ => ENNReal.ofReal (Real.exp (-(N * ∑ i, u i ^ 2))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((measurable_const.mul
        (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2)).neg))
    have hm2 : Measurable fun w : Fin D → ℝ => ENNReal.ofReal (Real.exp (-(N * G w))) := by
      fun_prop
    rw [← lintegral_prod_mul hm1.aemeasurable hm2.aemeasurable]
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; ring
  rw [hsplit, lintegral_exp_neg_sum_sq a hN]
  refine (mul_le_mul' le_rfl
    (lintegral_exp_le_of_angularMargin hD hd hG hs hM hmargin hA hN)).trans (le_of_eq ?_)
  have hm0 : 0 ≤ marginConst D d s M := by
    unfold marginConst
    have : (D : ℝ) < 2 * d * s := hmargin
    have := Real.log_pos one_lt_two
    have : 0 < (2 * d * s - D : ℝ) := by linarith
    positivity
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [rate, Nat.sub_self, pow_zero, mul_one]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    Real.div_rpow Real.pi_pos.le hN.le, neg_add, Real.rpow_add hN]
  rw [show (1 / 2 : ℝ) * a = a / 2 by ring, Real.rpow_neg hN.le ((a : ℝ) / 2)]
  field_simp

/-- **The margin template (T2), upper half.** If `Z N ≤ P · model(κ N)` eventually, where the model
has `a` regular active coordinates and an inactive loss `G` with a strict angular margin
(`AngularMargin`, `2 d s > D`), then `Z` has upper rate `(a/2 + D/(2d), 1)`: no logarithm. -/
theorem laplaceUpper_of_angularMargin {Z : ℝ → ℝ≥0∞} {a D d : ℕ} (hD : 1 ≤ D) (hd : 1 ≤ d)
    {G : (Fin D → ℝ) → ℝ} (hG : Measurable G) {s ε M κ : ℝ} {P : ℝ≥0∞} (hP : P ≠ ⊤)
    (hκ : 0 < κ) (hs : 0 < s) (hM : 0 ≤ M) (hmargin : (D : ℝ) < 2 * d * s)
    (hA : AngularMargin G d s ε M)
    (hcmp : ∀ᶠ N in atTop, Z N ≤ P * marginModel (a := a) G ε (κ * N)) :
    LaplaceUpper Z ((a : ℝ) / 2 + D / (2 * d)) 1 :=
  (((marginModel_laplaceUpper (a := a) hD hd hG hs hM hmargin hA).comp_mul hκ).const_mul
    hP).mono hcmp

/-- **The margin template (T2).** A lower-bound core at the same rate, a comparison with the model,
and the angular margin give the learning pair `(a/2 + D/(2d), 1)`. -/
theorem hasLaplacePair_of_angularMargin {Z : ℝ → ℝ≥0∞} {a D d : ℕ} (hD : 1 ≤ D) (hd : 1 ≤ d)
    {G : (Fin D → ℝ) → ℝ} (hG : Measurable G) {s ε M κ : ℝ} {P : ℝ≥0∞} (hP : P ≠ ⊤)
    (hκ : 0 < κ) (hs : 0 < s) (hM : 0 ≤ M) (hmargin : (D : ℝ) < 2 * d * s)
    (hA : AngularMargin G d s ε M)
    (hlow : LaplaceLower Z ((a : ℝ) / 2 + D / (2 * d)) 1)
    (hcmp : ∀ᶠ N in atTop, Z N ≤ P * marginModel (a := a) G ε (κ * N)) :
    HasLaplacePair Z ((a : ℝ) / 2 + D / (2 * d)) 1 :=
  ⟨le_rfl, hlow, laplaceUpper_of_angularMargin hD hd hG hP hκ hs hM hmargin hA hcmp⟩

/-- **Sanity: the named hypothesis is satisfiable.** `G(w) = ‖w‖^{2d}` has the angular margin
for every `s ≥ 0`, with `H(r, ξ) = ‖ξ‖^{2d}` and `M = 2^{2ds} · 2ᴰ`. -/
theorem angularMargin_norm_pow (D d : ℕ) {s : ℝ} (hs : 0 ≤ s) (ε : ℝ) :
    AngularMargin (fun w : Fin D → ℝ => ‖w‖ ^ (2 * d)) d s ε (2 ^ (2 * d * s) * 2 ^ D) := by
  refine ⟨fun _ ξ => ‖ξ‖ ^ (2 * d), fun r hr _ ξ _ => ⟨?_, by positivity⟩, fun r _ _ => ?_⟩
  · simp only
    rw [norm_smul, Real.norm_of_nonneg hr.le, mul_pow]
  · have hpt : ∀ ξ ∈ shell D, ENNReal.ofReal (‖ξ‖ ^ (2 * d)) ^ (-s) ≤
        ENNReal.ofReal (2 ^ (2 * d * s)) := by
      intro ξ hξ
      have h2 : (1 / 2 : ℝ) ^ (2 * d) ≤ ‖ξ‖ ^ (2 * d) := pow_le_pow_left₀ (by norm_num) hξ.1 _
      have h0 : (0 : ℝ) < (1 / 2) ^ (2 * d) := by positivity
      calc ENNReal.ofReal (‖ξ‖ ^ (2 * d)) ^ (-s)
          = ENNReal.ofReal ((‖ξ‖ ^ (2 * d)) ^ (-s)) :=
            ENNReal.ofReal_rpow_of_pos (h0.trans_le h2)
        _ ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ (2 * d)) ^ (-s)) :=
            ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos h0 h2 (by linarith))
        _ = ENNReal.ofReal (2 ^ (2 * d * s)) := by
            congr 1
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div,
              Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
            push_cast; ring_nf
    calc ∫⁻ ξ in shell D, ENNReal.ofReal (‖ξ‖ ^ (2 * d)) ^ (-s)
        ≤ ∫⁻ _ in shell D, ENNReal.ofReal (2 ^ (2 * d * s)) :=
          setLIntegral_mono' (measurableSet_shell D) hpt
      _ = ENNReal.ofReal (2 ^ (2 * d * s)) * volume (shell D) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (2 ^ (2 * d * s)) * ENNReal.ofReal (2 ^ D) := by
          gcongr; exact volume_shell_le D
      _ = ENNReal.ofReal (2 ^ (2 * d * s) * 2 ^ D) := (ENNReal.ofReal_mul (by positivity)).symm

end SLT.Template
