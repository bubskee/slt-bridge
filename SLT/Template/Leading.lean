/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Template.Margin

/-!
# Leading map plus higher-weight remainder (brief 03, T3)

The interface for new architectures. Suppose a loss `G` near a point has a **leading part** `G₀`
with three properties:
* `G₀` is homogeneous of degree `2d`: `G₀(a w) = a^{2d} G₀(w)` for `a ≥ 0`. This is the squared
  norm of a weight-`d` leading map;
* `G₀` is continuous;
* `G₀` is **nondegenerate**: positive away from `0`, so the leading map has an isolated zero.

Suppose also the **remainder has higher weight**: `|G(w) - G₀(w)| ≤ C ‖w‖^{2d+1}` near `0`. Then
`Z(N) = ∫_{‖w‖ ≤ δ} e^{-N G}` has learning pair `(D/(2d), 1)` (`hasLaplacePair_of_leading`). The
remainder does not change the pair, and every hypothesis is a checkable inequality on explicit
functions.

The route is the margin template (T2) with the named hypothesis **discharged**:
* `shell_bounds_of_homogeneous`: by compactness, `c ≤ G₀ ≤ C₀` on the shell;
* `angularMargin_of_leading`: the remainder perturbs the angular part by `O(r)`, so
  `G(rξ)/r^{2d} ≥ c/2` and the angular margin holds for every `s`;
* `laplaceUpper_of_leading`: the upper half, from the radial split;
* `laplaceLower_of_leading`: the lower half, from a ball of radius `N^{-1/(2d)}`.

**Not covered here: the degenerate case.** If the leading map has nonzero zeros (as for the shear
network's inactive map, or a block `u v³`), nondegeneracy fails. A remainder of higher weight can
then destroy the angular margin, and no elementary perturbation argument controls it. That case
needs a stability theorem; see `docs/T3_obstruction.md`. The named hypothesis `AngularMargin` (T2)
remains the interface there.
-/

@[expose] public section

namespace SLT.Template

open MeasureTheory Set Real Filter Metric
open scoped ENNReal

variable {D : ℕ}

/-- `G₀` is homogeneous of degree `k` under nonnegative scalings. -/
def IsHomogeneous (G₀ : (Fin D → ℝ) → ℝ) (k : ℕ) : Prop :=
  ∀ a : ℝ, 0 ≤ a → ∀ w, G₀ (a • w) = a ^ k * G₀ w

/-- The remainder `G - G₀` has weight above `2d` on `‖w‖ ≤ ε`. -/
def HigherWeightRemainder (G G₀ : (Fin D → ℝ) → ℝ) (d : ℕ) (C ε : ℝ) : Prop :=
  ∀ w, ‖w‖ ≤ ε → |G w - G₀ w| ≤ C * ‖w‖ ^ (2 * d + 1)

/-- **Compactness on the shell.** A continuous `G₀`, positive away from `0`, is bounded below by
some `c > 0` on the shell, and is at most some `C₀` on the closed unit ball. -/
theorem shell_bounds_of_homogeneous (hD : 1 ≤ D) {G₀ : (Fin D → ℝ) → ℝ} (hc : Continuous G₀)
    (hpos : ∀ w, w ≠ 0 → 0 < G₀ w) :
    (∃ c : ℝ, 0 < c ∧ ∀ ξ ∈ shell D, c ≤ G₀ ξ) ∧
      ∃ C₀ : ℝ, ∀ ξ ∈ closedBall (0 : Fin D → ℝ) 1, G₀ ξ ≤ C₀ := by
  constructor
  · set K : Set (Fin D → ℝ) := {ξ | 1 / 2 ≤ ‖ξ‖} ∩ closedBall 0 1
    have hK : IsCompact K :=
      (isCompact_closedBall 0 1).inter_left (isClosed_le continuous_const continuous_norm)
    have hne : K.Nonempty := by
      refine ⟨fun _ => 1, ?_, ?_⟩
      · change 1 / 2 ≤ ‖(fun _ => (1 : ℝ) : Fin D → ℝ)‖
        have : ‖(fun _ => (1 : ℝ) : Fin D → ℝ)‖ = 1 := by
          have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
          rw [pi_norm_const, norm_one]
        rw [this]; norm_num
      · rw [mem_closedBall_zero_iff]
        have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
        rw [pi_norm_const, norm_one]
    obtain ⟨ξ₀, hξ₀, hmin⟩ := hK.exists_isMinOn hne hc.continuousOn
    have hξ₀0 : ξ₀ ≠ 0 := by
      intro h; have := hξ₀.1; rw [h] at this
      simp only [mem_ofPred_eq, norm_zero] at this; norm_num at this
    refine ⟨G₀ ξ₀, hpos ξ₀ hξ₀0, fun ξ hξ => ?_⟩
    exact hmin ⟨hξ.1, mem_closedBall_zero_iff.mpr hξ.2.le⟩
  · obtain ⟨ξ₁, -, hmax⟩ := (isCompact_closedBall (0 : Fin D → ℝ) 1).exists_isMaxOn
      ⟨0, mem_closedBall_self zero_le_one⟩ hc.continuousOn
    exact ⟨G₀ ξ₁, fun ξ hξ => hmax hξ⟩

/-- A homogeneous `G₀` bounded by `C₀` on the unit ball satisfies `G₀ w ≤ C₀ ‖w‖^k`. -/
theorem le_of_homogeneous {G₀ : (Fin D → ℝ) → ℝ} {k : ℕ} (hk : 1 ≤ k) (hhom : IsHomogeneous G₀ k)
    {C₀ : ℝ} (hC₀ : ∀ ξ ∈ closedBall (0 : Fin D → ℝ) 1, G₀ ξ ≤ C₀) (w : Fin D → ℝ) :
    G₀ w ≤ C₀ * ‖w‖ ^ k := by
  rcases eq_or_ne w 0 with rfl | hw
  · have h0 := hhom 0 le_rfl 0
    rw [zero_smul, zero_pow (by omega), zero_mul] at h0
    rw [h0, norm_zero, zero_pow (by omega), mul_zero]
  · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have e : w = ‖w‖ • (‖w‖⁻¹ • w) := by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hu : ‖w‖⁻¹ • w ∈ closedBall (0 : Fin D → ℝ) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    rw [e, hhom _ hn.le, norm_smul, norm_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ hn.ne', mul_one, mul_comm C₀]
    exact mul_le_mul_of_nonneg_left (hC₀ _ hu) (pow_nonneg hn.le _)

/-- **The angular margin is discharged by a nondegenerate leading part.** If `c ≤ G₀` on the
shell, `G₀` is homogeneous of degree `2d`, the remainder has higher weight with constant `C ≥ 0` on
`‖w‖ ≤ ε`, and `C ε ≤ c/2`, then `AngularMargin G d s ε ((c/2)^{-s} · 2ᴰ)` holds for every
`s ≥ 0`. -/
theorem angularMargin_of_leading {G G₀ : (Fin D → ℝ) → ℝ} {d : ℕ} {c C ε s : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) (hs : 0 ≤ s) (hhom : IsHomogeneous G₀ (2 * d))
    (hshell : ∀ ξ ∈ shell D, c ≤ G₀ ξ) (hrem : HigherWeightRemainder G G₀ d C ε)
    (hCε : C * ε ≤ c / 2) :
    AngularMargin G d s ε ((c / 2) ^ (-s) * 2 ^ D) := by
  have hlow : ∀ r : ℝ, 0 < r → r ≤ ε → ∀ ξ ∈ shell D, c / 2 ≤ G (r • ξ) / r ^ (2 * d) := by
    intro r hr hrε ξ hξ
    have hn : ‖r • ξ‖ = r * ‖ξ‖ := by rw [norm_smul, Real.norm_of_nonneg hr.le]
    have hξ1 : ‖ξ‖ ≤ 1 := hξ.2.le
    have hξ0 : 0 ≤ ‖ξ‖ := norm_nonneg _
    have hle : ‖r • ξ‖ ≤ ε := by rw [hn]; nlinarith
    have h1 := (abs_le.mp (hrem _ hle)).1
    rw [hhom r hr.le] at h1
    have hpow : ‖r • ξ‖ ^ (2 * d + 1) ≤ r ^ (2 * d) * r := by
      rw [hn, pow_succ, mul_pow]
      have : ‖ξ‖ ^ (2 * d) ≤ 1 := pow_le_one₀ hξ0 hξ1
      have h2 : r * ‖ξ‖ ≤ r := by nlinarith
      calc r ^ (2 * d) * ‖ξ‖ ^ (2 * d) * (r * ‖ξ‖) ≤ r ^ (2 * d) * 1 * r := by
            gcongr
        _ = r ^ (2 * d) * r := by ring
    have hrd : 0 < r ^ (2 * d) := pow_pos hr _
    rw [le_div_iff₀ hrd]
    have h3 : C * ‖r • ξ‖ ^ (2 * d + 1) ≤ C * (r ^ (2 * d) * r) := mul_le_mul_of_nonneg_left hpow hC
    have h4 : C * r ≤ c / 2 := (mul_le_mul_of_nonneg_left hrε hC).trans hCε
    have h5 := hshell ξ hξ
    nlinarith
  refine ⟨fun r ξ => G (r • ξ) / r ^ (2 * d), fun r hr hrε ξ hξ => ⟨?_, ?_⟩, fun r hr hrε => ?_⟩
  · field_simp
  · exact (by linarith : (0 : ℝ) ≤ c / 2).trans (hlow r hr hrε ξ hξ)
  · have hpt : ∀ ξ ∈ shell D, ENNReal.ofReal (G (r • ξ) / r ^ (2 * d)) ^ (-s) ≤
        ENNReal.ofReal ((c / 2) ^ (-s)) := by
      intro ξ hξ
      have h := hlow r hr hrε ξ hξ
      have hc2 : 0 < c / 2 := by linarith
      rw [ENNReal.ofReal_rpow_of_pos (hc2.trans_le h)]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hc2 h (by linarith))
    calc ∫⁻ ξ in shell D, ENNReal.ofReal (G (r • ξ) / r ^ (2 * d)) ^ (-s)
        ≤ ∫⁻ _ in shell D, ENNReal.ofReal ((c / 2) ^ (-s)) :=
          setLIntegral_mono' (measurableSet_shell D) hpt
      _ = ENNReal.ofReal ((c / 2) ^ (-s)) * volume (shell D) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal ((c / 2) ^ (-s)) * ENNReal.ofReal (2 ^ D) := by
          gcongr; exact volume_shell_le D
      _ = ENNReal.ofReal ((c / 2) ^ (-s) * 2 ^ D) := (ENNReal.ofReal_mul (by positivity)).symm

/-- **Upper half.** Under a nondegenerate leading part (`c ≤ G₀` on the shell) and a higher-weight
remainder with `C ε ≤ c/2`, `∫_{‖w‖ ≤ ε/2} e^{-N G}` has upper rate `(D/(2d), 1)`. -/
theorem laplaceUpper_of_leading (hD : 1 ≤ D) {G G₀ : (Fin D → ℝ) → ℝ} (hG : Measurable G) {d : ℕ}
    (hd : 1 ≤ d) {c C ε : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hhom : IsHomogeneous G₀ (2 * d))
    (hshell : ∀ ξ ∈ shell D, c ≤ G₀ ξ) (hrem : HigherWeightRemainder G G₀ d C ε)
    (hCε : C * ε ≤ c / 2) :
    LaplaceUpper (fun N => ∫⁻ w in closedBall (0 : Fin D → ℝ) (ε / 2),
      ENNReal.ofReal (Real.exp (-(N * G w)))) ((D : ℝ) / (2 * d)) 1 := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set s : ℝ := D / d
  have hs : 0 < s := by positivity
  have hmargin : (D : ℝ) < 2 * d * s := by
    have : 2 * (d : ℝ) * s = 2 * D := by simp only [s]; field_simp
    linarith
  have hA := angularMargin_of_leading (s := s) hc hC hs.le hhom hshell hrem hCε
  refine ⟨marginConst D d s ((c / 2) ^ (-s) * 2 ^ D), ?_⟩
  filter_upwards [eventually_gt_atTop 0] with N hN
  refine (lintegral_exp_le_of_angularMargin hD hd hG hs (by positivity) hmargin hA hN).trans
    (le_of_eq ?_)
  simp [rate]

/-- **Lower half.** If `G ≤ K ‖w‖^{2d}` on `‖w‖ ≤ ε/2`, then `∫_{‖w‖ ≤ ε/2} e^{-N G}` has lower rate
`(D/(2d), 1)`, with a ball of radius `N^{-1/(2d)}`. -/
theorem laplaceLower_of_leading {G : (Fin D → ℝ) → ℝ} {d : ℕ} (hd : 1 ≤ d) {K ε : ℝ}
    (hε : 0 < ε) (hK : 0 ≤ K) (hup : ∀ w, ‖w‖ ≤ ε / 2 → G w ≤ K * ‖w‖ ^ (2 * d)) :
    LaplaceLower (fun N => ∫⁻ w in closedBall (0 : Fin D → ℝ) (ε / 2),
      ENNReal.ofReal (Real.exp (-(N * G w)))) ((D : ℝ) / (2 * d)) 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨Real.exp (-K) * 2 ^ D, by positivity, ?_⟩
  have hρt : Tendsto (fun N : ℝ => N ^ (-(1 / (2 * (d : ℝ))))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by positivity)
  filter_upwards [eventually_gt_atTop 0, hρt.eventually (ge_mem_nhds (half_pos hε))]
    with N hN hρ
  set ρ := N ^ (-(1 / (2 * (d : ℝ))))
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hN _
  have hρd : ρ ^ (2 * d) = N⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    push_cast
    rw [show -(1 / (2 * (d : ℝ))) * (2 * d) = -1 by field_simp, Real.rpow_neg_one]
  have hρD : ρ ^ D = N ^ (-((D : ℝ) / (2 * d))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; congr 1; field_simp
  calc ENNReal.ofReal (Real.exp (-K) * 2 ^ D * rate ((D : ℝ) / (2 * d)) 1 N)
      = ENNReal.ofReal (Real.exp (-K)) * volume (closedBall (0 : Fin D → ℝ) ρ) := by
        rw [Real.volume_pi_closedBall 0 hρ0.le, Fintype.card_fin, ← ENNReal.ofReal_mul
          (Real.exp_pos _).le]
        congr 1
        simp only [rate, Nat.sub_self, pow_zero, mul_one]
        rw [mul_pow, hρD]; ring
    _ = ∫⁻ _ in closedBall (0 : Fin D → ℝ) ρ, ENNReal.ofReal (Real.exp (-K)) :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ w in closedBall (0 : Fin D → ℝ) ρ, ENNReal.ofReal (Real.exp (-(N * G w))) := by
        refine setLIntegral_mono' isClosed_closedBall.measurableSet fun w hw => ?_
        have hw' : ‖w‖ ≤ ρ := mem_closedBall_zero_iff.mp hw
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have h1 := hup w (hw'.trans hρ)
        have h2 : ‖w‖ ^ (2 * d) ≤ ρ ^ (2 * d) := pow_le_pow_left₀ (norm_nonneg _) hw' _
        have h3 : N * (K * ‖w‖ ^ (2 * d)) ≤ N * (K * N⁻¹) := by
          rw [← hρd]; gcongr
        rw [show N * (K * N⁻¹) = K by field_simp] at h3
        nlinarith [mul_le_mul_of_nonneg_left h1 hN.le]
    _ ≤ ∫⁻ w in closedBall (0 : Fin D → ℝ) (ε / 2), ENNReal.ofReal (Real.exp (-(N * G w))) :=
        lintegral_mono_set (closedBall_subset_closedBall hρ)

/-- **Leading map plus higher-weight remainder (T3).** Let `G₀` be continuous, positive away from
`0`, and homogeneous of degree `2d`. Let `G` be measurable with `|G - G₀| ≤ C ‖w‖^{2d+1}` on
`‖w‖ ≤ ε`, and let `c ≤ G₀` on the shell with `C ε ≤ c/2`. Then `∫_{‖w‖ ≤ ε/2} e^{-N G}` has
learning pair `(D/(2d), 1)`: the remainder does not change the pair. -/
theorem hasLaplacePair_of_leading (hD : 1 ≤ D) {G G₀ : (Fin D → ℝ) → ℝ} (hG : Measurable G)
    (hG₀ : Continuous G₀) {d : ℕ} (hd : 1 ≤ d) {c C ε : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hC : 0 ≤ C) (hhom : IsHomogeneous G₀ (2 * d)) (hshell : ∀ ξ ∈ shell D, c ≤ G₀ ξ)
    (hrem : HigherWeightRemainder G G₀ d C ε) (hCε : C * ε ≤ c / 2) :
    HasLaplacePair (fun N => ∫⁻ w in closedBall (0 : Fin D → ℝ) (ε / 2),
      ENNReal.ofReal (Real.exp (-(N * G w)))) ((D : ℝ) / (2 * d)) 1 := by
  refine ⟨le_rfl, ?_, laplaceUpper_of_leading hD hG hd hc hC hhom hshell hrem hCε⟩
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, ∀ ξ ∈ closedBall (0 : Fin D → ℝ) 1, G₀ ξ ≤ C₀ :=
    (isCompact_closedBall (0 : Fin D → ℝ) 1).exists_isMaxOn
      ⟨0, mem_closedBall_self zero_le_one⟩ hG₀.continuousOn |>.elim fun ξ₁ h =>
        ⟨G₀ ξ₁, fun ξ hξ => h.2 hξ⟩
  have hC₀0 : 0 ≤ C₀ := by
    have h0 := hhom 0 le_rfl 0
    rw [zero_smul, zero_pow (by omega), zero_mul] at h0
    have := hC₀ 0 (mem_closedBall_self zero_le_one); linarith
  refine laplaceLower_of_leading hd hε (K := C₀ + C * ε) (by positivity) fun w hw => ?_
  have hwε : ‖w‖ ≤ ε := hw.trans (by linarith)
  have h1 := (abs_le.mp (hrem w hwε)).2
  have h2 := le_of_homogeneous (by omega) hhom hC₀ w
  have h3 : C * ‖w‖ ^ (2 * d + 1) ≤ C * ε * ‖w‖ ^ (2 * d) :=
    calc C * ‖w‖ ^ (2 * d + 1) = C * ‖w‖ * ‖w‖ ^ (2 * d) := by ring
      _ ≤ C * ε * ‖w‖ ^ (2 * d) := by gcongr
  nlinarith

/-- **Leading map plus remainder, local form.** Under the same structural hypotheses, but without
naming `c`, the pair `(D/(2d), 1)` holds on every small enough ball. -/
theorem exists_hasLaplacePair_of_leading (hD : 1 ≤ D) {G G₀ : (Fin D → ℝ) → ℝ}
    (hG : Measurable G) (hG₀ : Continuous G₀) (hpos : ∀ w, w ≠ 0 → 0 < G₀ w) {d : ℕ}
    (hd : 1 ≤ d) {C ε : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) (hhom : IsHomogeneous G₀ (2 * d))
    (hrem : HigherWeightRemainder G G₀ d C ε) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε₀ →
      HasLaplacePair (fun N => ∫⁻ w in closedBall (0 : Fin D → ℝ) (δ / 2),
        ENNReal.ofReal (Real.exp (-(N * G w)))) ((D : ℝ) / (2 * d)) 1 := by
  obtain ⟨⟨c, hc, hshell⟩, -⟩ := shell_bounds_of_homogeneous hD hG₀ hpos
  refine ⟨min ε (c / (2 * (C + 1))), lt_min hε (by positivity), fun δ hδ hδε => ?_⟩
  have hδ1 : δ ≤ ε := hδε.trans (min_le_left _ _)
  have hδ2 : δ ≤ c / (2 * (C + 1)) := hδε.trans (min_le_right _ _)
  refine hasLaplacePair_of_leading hD hG hG₀ hd hδ hc hC hhom hshell
    (fun w hw => hrem w (hw.trans hδ1)) ?_
  have : C * δ ≤ (C + 1) * δ := by nlinarith
  calc C * δ ≤ (C + 1) * δ := this
    _ ≤ (C + 1) * (c / (2 * (C + 1))) := by gcongr
    _ = c / 2 := by field_simp

end SLT.Template
