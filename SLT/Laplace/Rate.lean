/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Mathlib

/-!
# Laplace rates `N^{-λ} (log N)^{m-1}`

The rate `rate λ m N = N^{-λ} (log N)^{m-1}` of the SLT asymptotic `Z(N) ≍ N^{-λ}(log N)^{m-1}`, and
the order on rates: `Dominates λ m λ' m'` says that the `(λ', m')` rate is eventually at most the
`(λ, m)` rate (`λ < λ'`, or `λ = λ'` and `m' ≤ m`).

`rate` has the same body as `ResidualSLT.laplaceRate` (scalar library) and as grammar's
`powerLogRate λ (m-1)`.
-/

@[expose] public section

namespace SLT

open Filter Asymptotics Real

/-- The Laplace rate `N^{-λ} (log N)^{m-1}`. -/
noncomputable def rate (lam : ℝ) (m : ℕ) (N : ℝ) : ℝ := N ^ (-lam) * Real.log N ^ (m - 1)

/-- `(λ, m)` dominates `(λ', m')`: the rate `N^{-λ'}(log N)^{m'-1}` is eventually at most
`N^{-λ}(log N)^{m-1}`. -/
def Dominates (lam : ℝ) (m : ℕ) (lam' : ℝ) (m' : ℕ) : Prop :=
  lam < lam' ∨ (lam = lam' ∧ m' ≤ m)

theorem Dominates.refl (lam : ℝ) (m : ℕ) : Dominates lam m lam m := Or.inr ⟨rfl, le_rfl⟩

theorem rate_nonneg (lam : ℝ) (m : ℕ) {N : ℝ} (hN : 1 ≤ N) : 0 ≤ rate lam m N :=
  mul_nonneg (Real.rpow_nonneg (by linarith) _) (pow_nonneg (Real.log_nonneg hN) _)

theorem rate_pos (lam : ℝ) (m : ℕ) {N : ℝ} (hN : 1 < N) : 0 < rate lam m N :=
  mul_pos (Real.rpow_pos_of_pos (by linarith) _) (pow_pos (Real.log_pos hN) _)

theorem eventually_rate_nonneg (lam : ℝ) (m : ℕ) : ∀ᶠ N in atTop, 0 ≤ rate lam m N :=
  (eventually_ge_atTop 1).mono fun _ hN => rate_nonneg lam m hN

theorem eventually_rate_pos (lam : ℝ) (m : ℕ) : ∀ᶠ N in atTop, 0 < rate lam m N :=
  (eventually_gt_atTop 1).mono fun _ hN => rate_pos lam m hN

theorem one_le_log_of_exp_le {N : ℝ} (hN : Real.exp 1 ≤ N) : 1 ≤ Real.log N := by
  rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hN

theorem eventually_one_le_log : ∀ᶠ N : ℝ in atTop, 1 ≤ Real.log N :=
  (eventually_ge_atTop (Real.exp 1)).mono fun _ hN => one_le_log_of_exp_le hN

/-- `N^{-λ} ≤ rate λ m N` once `log N ≥ 1`. -/
theorem rpow_neg_le_rate (lam : ℝ) (m : ℕ) {N : ℝ} (hN : Real.exp 1 ≤ N) :
    N ^ (-lam) ≤ rate lam m N := by
  have hl := one_le_log_of_exp_le hN
  have hN0 : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hN
  unfold rate
  calc N ^ (-lam) = N ^ (-lam) * 1 := (mul_one _).symm
    _ ≤ N ^ (-lam) * Real.log N ^ (m - 1) :=
      mul_le_mul_of_nonneg_left (one_le_pow₀ hl) (Real.rpow_nonneg hN0.le _)

theorem rpow_neg_isBigO_rate (lam : ℝ) (m : ℕ) :
    (fun N : ℝ => N ^ (-lam)) =O[atTop] rate lam m := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
  have hN0 : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hN
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hN0.le _),
    Real.norm_of_nonneg (rate_nonneg lam m (le_trans (by linarith [Real.add_one_le_exp (1:ℝ)]) hN)),
    one_mul]
  exact rpow_neg_le_rate lam m hN

/-- `(log N)^k = o(N^s)` for `s > 0`, with a natural power. -/
theorem log_pow_isLittleO_rpow (k : ℕ) {s : ℝ} (hs : 0 < s) :
    (fun N : ℝ => Real.log N ^ k) =o[atTop] fun N => N ^ s :=
  (isLittleO_log_rpow_rpow_atTop (k : ℝ) hs).congr_left fun _ => Real.rpow_natCast _ _

/-- **Strict domination is little-o.** If `λ < λ'`, or `λ = λ'` and `m' < m` (with `m' ≥ 1`), then
`rate λ' m' = o(rate λ m)`. -/
theorem rate_isLittleO {lam lam' : ℝ} {m m' : ℕ} (hm' : 1 ≤ m')
    (h : lam < lam' ∨ (lam = lam' ∧ m' < m)) : rate lam' m' =o[atTop] rate lam m := by
  rcases h with h | ⟨rfl, h⟩
  · have h1 := log_pow_isLittleO_rpow (m' - 1) (sub_pos.mpr h)
    have h2 := (isBigO_refl (fun N : ℝ => N ^ (-lam')) atTop).mul_isLittleO h1
    have h3 : (fun N : ℝ => N ^ (-lam') * N ^ (lam' - lam)) =O[atTop] rate lam m := by
      refine IsBigO.trans ?_ (rpow_neg_isBigO_rate lam m)
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      rw [← Real.rpow_add hN, show -lam' + (lam' - lam) = -lam by ring, one_mul]
    exact h2.trans_isBigO h3
  · have h1 : (fun N : ℝ => Real.log N ^ (m' - 1)) =o[atTop] fun N => Real.log N ^ (m - 1) :=
      (isLittleO_pow_pow_atTop_of_lt (by omega : m' - 1 < m - 1)).comp_tendsto
        Real.tendsto_log_atTop
    exact (isBigO_refl (fun N : ℝ => N ^ (-lam)) atTop).mul_isLittleO h1

/-- **Domination gives an eventual inequality of rates** (constant `1`). -/
theorem rate_le_of_dominates {lam lam' : ℝ} {m m' : ℕ} (h : Dominates lam m lam' m') :
    ∀ᶠ N in atTop, rate lam' m' N ≤ rate lam m N := by
  rcases h with h | ⟨rfl, h⟩
  · have h1 := (log_pow_isLittleO_rpow (m' - 1) (sub_pos.mpr h)).bound one_pos
    filter_upwards [h1, eventually_ge_atTop (Real.exp 1)] with N h1 hN
    have hN0 : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hN
    have hl := one_le_log_of_exp_le hN
    rw [Real.norm_of_nonneg (pow_nonneg (by linarith) _),
      Real.norm_of_nonneg (Real.rpow_nonneg hN0.le _), one_mul] at h1
    calc rate lam' m' N = N ^ (-lam') * Real.log N ^ (m' - 1) := rfl
      _ ≤ N ^ (-lam') * N ^ (lam' - lam) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hN0.le _)
      _ = N ^ (-lam) := by rw [← Real.rpow_add hN0]; ring_nf
      _ ≤ rate lam m N := rpow_neg_le_rate lam m hN
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
    have hN0 : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hN
    have hl := one_le_log_of_exp_le hN
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hl (by omega))
      (Real.rpow_nonneg hN0.le _)

/-- Exponential decay is `o` of every rate. -/
theorem exp_neg_isLittleO_rate {a : ℝ} (ha : 0 < a) (lam : ℝ) (m : ℕ) :
    (fun N : ℝ => Real.exp (-a * N)) =o[atTop] rate lam m :=
  (isLittleO_exp_neg_mul_rpow_atTop ha (-lam)).trans_isBigO (rpow_neg_isBigO_rate lam m)

/-- `rate (λ₁+λ₂) (m₁+m₂-1) = rate λ₁ m₁ · rate λ₂ m₂` for `N > 0`, `m₁, m₂ ≥ 1`. -/
theorem rate_add {l₁ l₂ : ℝ} {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) {N : ℝ} (hN : 0 < N) :
    rate (l₁ + l₂) (m₁ + m₂ - 1) N = rate l₁ m₁ N * rate l₂ m₂ N := by
  unfold rate
  rw [neg_add, Real.rpow_add hN, show m₁ + m₂ - 1 - 1 = (m₁ - 1) + (m₂ - 1) by omega, pow_add]
  ring

theorem rate_zero_one (N : ℝ) : rate 0 1 N = 1 := by simp [rate]

/-- For `C > 0`: eventually `(log N)/2 ≤ log(C N) ≤ 2 log N` and `0 ≤ log (C N)`. -/
theorem log_mul_bounds {C : ℝ} (hC : 0 < C) :
    ∀ᶠ N in atTop, 0 ≤ Real.log (C * N) ∧ Real.log N / 2 ≤ Real.log (C * N) ∧
      Real.log (C * N) ≤ 2 * Real.log N := by
  filter_upwards [eventually_ge_atTop (C⁻¹ ^ 2), eventually_ge_atTop C,
    eventually_ge_atTop C⁻¹, eventually_ge_atTop 1] with N h1 h2 h3 h4
  have hN0 : 0 < N := by linarith
  rw [Real.log_mul hC.ne' hN0.ne']
  have hlN : 0 ≤ Real.log N := Real.log_nonneg h4
  have a1 : -Real.log C ≤ Real.log N := by
    rw [← Real.log_inv]; exact Real.log_le_log (by positivity) h3
  have a2 : Real.log C ≤ Real.log N := Real.log_le_log hC h2
  have a3 : -2 * Real.log C ≤ Real.log N := by
    have := Real.log_le_log (by positivity) h1
    rw [Real.log_pow, Real.log_inv] at this; push_cast at this; linarith
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **Rescaling a rate.** For `b > 0`, eventually
`b^{-λ} 2^{-(m-1)} rate λ m N ≤ rate λ m (b N) ≤ b^{-λ} 2^{m-1} rate λ m N`. -/
theorem rate_comp_mul_bounds (lam : ℝ) (m : ℕ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ N in atTop, b ^ (-lam) * (1 / 2) ^ (m - 1) * rate lam m N ≤ rate lam m (b * N) ∧
      rate lam m (b * N) ≤ b ^ (-lam) * 2 ^ (m - 1) * rate lam m N := by
  filter_upwards [log_mul_bounds hb, eventually_ge_atTop 1] with N ⟨l0, l1, l2⟩ hN
  have hN0 : 0 < N := by linarith
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hp : 0 ≤ b ^ (-lam) * N ^ (-lam) := by positivity
  unfold rate
  rw [Real.mul_rpow hb.le hN0.le]
  constructor
  · have : (1 / 2 : ℝ) ^ (m - 1) * Real.log N ^ (m - 1) ≤ Real.log (b * N) ^ (m - 1) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
    calc b ^ (-lam) * (1 / 2) ^ (m - 1) * (N ^ (-lam) * Real.log N ^ (m - 1))
        = (b ^ (-lam) * N ^ (-lam)) * ((1 / 2) ^ (m - 1) * Real.log N ^ (m - 1)) := by ring
      _ ≤ (b ^ (-lam) * N ^ (-lam)) * Real.log (b * N) ^ (m - 1) :=
        mul_le_mul_of_nonneg_left this hp
  · have : Real.log (b * N) ^ (m - 1) ≤ 2 ^ (m - 1) * Real.log N ^ (m - 1) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ l0 l2 _
    calc b ^ (-lam) * N ^ (-lam) * Real.log (b * N) ^ (m - 1)
        ≤ (b ^ (-lam) * N ^ (-lam)) * (2 ^ (m - 1) * Real.log N ^ (m - 1)) :=
          mul_le_mul_of_nonneg_left this hp
      _ = _ := by ring

end SLT
