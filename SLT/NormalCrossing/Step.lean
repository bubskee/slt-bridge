/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Mathlib

/-!
# Normal crossing: the one-coordinate step

The one-dimensional step `G(N) = ∫₀¹ x^h F(N x^k) dx` of the normal-crossing induction, for any
exponent `k ≥ 1`. It combines bounds for `F` at `(λ', m')` with `μ = (h+1)/k`: the result is
`(min λ' μ, m' + [μ = λ'])` if `μ ≥ λ'`, and `(μ, 1)` if `μ < λ'`.

Ported from `vector-slt-lean` `VectorSLT/SLT/NormalCrossing.lean` (b21c0ad), where the exponent
was `2k`. The proofs only use that the exponent is a positive natural number.
-/

@[expose] public section


namespace SLT.NC

open MeasureTheory Set Filter Real

/-! ### Explicit one-dimensional integrals -/

theorem lintegral_Ioc_zero_rpow {a h : ℝ} (ha : 0 ≤ a) (hh : -1 < h) :
    ∫⁻ x in Ioc 0 a, ENNReal.ofReal (x ^ h) = ENNReal.ofReal (a ^ (h + 1) / (h + 1)) := by
  have hint : IntegrableOn (fun x : ℝ => x ^ h) (Ioc 0 a) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha).mp (intervalIntegral.intervalIntegrable_rpow' hh)
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · rw [← intervalIntegral.integral_of_le ha, integral_rpow (Or.inl hh),
      Real.zero_rpow (by linarith), sub_zero]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact Real.rpow_nonneg hx.1.le _

theorem lintegral_Ioc_one_rpow {a e : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (he : e ≠ -1) :
    ∫⁻ x in Ioc a 1, ENNReal.ofReal (x ^ e) = ENNReal.ofReal ((1 - a ^ (e + 1)) / (e + 1)) := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ e) (Icc a 1) :=
    fun x hx => (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hx.1]))).continuousWithinAt
  have hint : IntegrableOn (fun x : ℝ => x ^ e) (Ioc a 1) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · rw [← intervalIntegral.integral_of_le ha1, integral_rpow (Or.inr ⟨he, ?_⟩), Real.one_rpow]
    rw [Set.uIcc_of_le ha1]; exact fun h0 => by linarith [h0.1]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact Real.rpow_nonneg (by linarith [hx.1]) _

theorem lintegral_Ioc_one_inv {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∫⁻ x in Ioc a 1, ENNReal.ofReal (x ^ (-1 : ℝ)) = ENNReal.ofReal (Real.log (1 / a)) := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ (-1 : ℝ)) (Icc a 1) :=
    fun x hx => (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hx.1]))).continuousWithinAt
  have hint : IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Ioc a 1) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · rw [← intervalIntegral.integral_of_le ha1]
    simp_rw [Real.rpow_neg_one]
    rw [integral_inv_of_pos ha one_pos]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact Real.rpow_nonneg (by linarith [hx.1]) _

/-- `(1 + log y)^j ≤ D y^ε` for `y ≥ 1`. -/
theorem one_add_log_pow_le {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y : ℝ, 1 ≤ y → (1 + Real.log y) ^ j ≤ D * y ^ ε := by
  set δ := ε / (j + 1)
  have hδ : 0 < δ := by positivity
  refine ⟨(1 + 1 / δ) ^ j, by positivity, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  have h1 : 1 + Real.log y ≤ (1 + 1 / δ) * y ^ δ := by
    have hl := Real.log_le_rpow_div hy0.le hδ
    have hyδ : 1 ≤ y ^ δ := Real.one_le_rpow hy hδ.le
    have : (1 + 1 / δ) * y ^ δ = y ^ δ + y ^ δ / δ := by ring
    rw [this]; linarith
  have h2 : (1 + Real.log y) ^ j ≤ ((1 + 1 / δ) * y ^ δ) ^ j :=
    pow_le_pow_left₀ (by linarith [Real.log_nonneg hy]) h1 j
  rw [mul_pow] at h2
  refine h2.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
  apply Real.rpow_le_rpow_of_exponent_le hy
  simp only [δ]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

/-! ### The one-dimensional step -/

/-- The bounds carried through the induction: antitone on `[0,∞)`, finite at `0`, positive at
`1`, and a pair `(λ, m)` in the form `upper: C M^{-λ}(1+log M)^{m-1}` for `M ≥ 1`,
`lower: c M^{-λ}(log M)^{m-1}` for `M ≥ M₀`. -/
def NCBound (F : ℝ → ENNReal) (lam : ℝ) (m : ℕ) : Prop :=
  (∀ M M', 0 ≤ M → M ≤ M' → F M' ≤ F M) ∧ (∃ B : ℝ, F 0 ≤ ENNReal.ofReal B) ∧
  (∃ b : ℝ, 0 < b ∧ ENNReal.ofReal b ≤ F 1) ∧
  (∃ C : ℝ, ∀ M, 1 ≤ M → F M ≤ ENNReal.ofReal (C * M ^ (-lam) * (1 + Real.log M) ^ (m - 1))) ∧
  (∃ c : ℝ, 0 < c ∧ ∃ M₀ : ℝ, ∀ M, M₀ ≤ M →
    ENNReal.ofReal (c * M ^ (-lam) * Real.log M ^ (m - 1)) ≤ F M)

/-- One peeled coordinate: `G(N) = ∫_{(0,1]} x^h F(N x^{k}) dx`. -/
noncomputable def stepG (F : ℝ → ENNReal) (h : ℝ) (k : ℕ) (N : ℝ) : ENNReal :=
  ∫⁻ x in Ioc 0 1, ENNReal.ofReal (x ^ h) * F (N * x ^ k)

section Step

variable {F : ℝ → ENNReal} {h : ℝ} {k : ℕ}

theorem stepG_mono (hF : ∀ M M', 0 ≤ M → M ≤ M' → F M' ≤ F M) {N N' : ℝ} (hN : 0 ≤ N)
    (hNN : N ≤ N') : stepG F h k N' ≤ stepG F h k N := by
  apply setLIntegral_mono' measurableSet_Ioc
  intro x hx
  have hx0 : 0 ≤ x ^ k := pow_nonneg hx.1.le _
  gcongr
  exact hF _ _ (mul_nonneg hN hx0) (mul_le_mul_of_nonneg_right hNN hx0)

theorem stepG_zero_le (hh : -1 < h) {B : ℝ} (hB : F 0 ≤ ENNReal.ofReal B) :
    stepG F h k 0 ≤ ENNReal.ofReal (B / (h + 1)) := by
  unfold stepG
  simp only [zero_mul]
  calc ∫⁻ x in Ioc 0 1, ENNReal.ofReal (x ^ h) * F 0
      ≤ ∫⁻ x in Ioc 0 1, ENNReal.ofReal (x ^ h) * ENNReal.ofReal B :=
        setLIntegral_mono' measurableSet_Ioc fun x _ => by gcongr
    _ = ENNReal.ofReal (B / (h + 1)) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_Ioc_zero_rpow zero_le_one hh,
          Real.one_rpow]
        rcases le_or_gt B 0 with hB0 | hB0
        · rw [ENNReal.ofReal_of_nonpos hB0, mul_zero,
            ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg hB0 (by linarith))]
        · have hh1 : 0 < h + 1 := by linarith
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring

/-- The split point `a = N^{-1/(k)}`: `N a^{k} = 1`. -/
theorem split_point {N : ℝ} (hN : 1 ≤ N) (hk : 1 ≤ k) :
    let a := N ^ (-(1 : ℝ) / k)
    0 < a ∧ a ≤ 1 ∧ N * a ^ k = 1 ∧ ∀ e : ℝ, a ^ e = N ^ (-e / k) := by
  intro a
  have hN0 : 0 < N := by linarith
  have hq : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨Real.rpow_pos_of_pos hN0 _, Real.rpow_le_one_of_one_le_of_nonpos hN
    (div_nonpos_of_nonpos_of_nonneg (by norm_num) hq.le), ?_, fun e => ?_⟩
  · simp only [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    rw [show -(1 : ℝ) / k * (k) = -1 by field_simp, Real.rpow_neg_one,
      mul_inv_cancel₀ hN0.ne']
  · simp only [a]; rw [← Real.rpow_mul hN0.le]; ring_nf

/-- **(L1)** `G(N) ≥ F(1) N^{-μ}/(h+1)` for `N ≥ 1`, `μ = (h+1)/(k)`. -/
theorem stepG_lower_mu (hF : ∀ M M', 0 ≤ M → M ≤ M' → F M' ≤ F M) (hh : -1 < h)
    (hk : 1 ≤ k) {b : ℝ} (_hb : 0 < b) (hb1 : ENNReal.ofReal b ≤ F 1) {N : ℝ} (hN : 1 ≤ N) :
    ENNReal.ofReal (b / (h + 1) * N ^ (-((h + 1) / k))) ≤ stepG F h k N := by
  obtain ⟨ha0, ha1, haN, hae⟩ := split_point hN hk
  set a := N ^ (-(1 : ℝ) / k)
  have hN0 : 0 < N := by linarith
  have hh1 : 0 < h + 1 := by linarith
  calc ENNReal.ofReal (b / (h + 1) * N ^ (-((h + 1) / k)))
      = ∫⁻ x in Ioc 0 a, ENNReal.ofReal (x ^ h) * ENNReal.ofReal b := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_Ioc_zero_rpow ha0.le hh,
          hae, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring_nf
    _ ≤ ∫⁻ x in Ioc 0 a, ENNReal.ofReal (x ^ h) * F (N * x ^ k) := by
        refine setLIntegral_mono' measurableSet_Ioc fun x hx => ?_
        gcongr
        refine hb1.trans (hF _ _ (by have := hx.1; positivity) ?_)
        rw [← haN]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1.le hx.2 _) hN0.le
    _ ≤ stepG F h k N := lintegral_mono_set (Ioc_subset_Ioc_right ha1)

/-- Splitting at `a`: the inner piece is at most `B N^{-μ}/(h+1)`. -/
theorem stepG_split_le (hF : ∀ M M', 0 ≤ M → M ≤ M' → F M' ≤ F M) (hh : -1 < h) (hk : 1 ≤ k)
    {B : ℝ} (hB : F 0 ≤ ENNReal.ofReal B) (_hB0 : 0 ≤ B) {N : ℝ} (hN : 1 ≤ N) :
    stepG F h k N ≤ ENNReal.ofReal (B / (h + 1) * N ^ (-((h + 1) / k))) +
      ∫⁻ x in Ioc (N ^ (-(1 : ℝ) / k)) 1, ENNReal.ofReal (x ^ h) * F (N * x ^ k) := by
  obtain ⟨ha0, ha1, haN, hae⟩ := split_point hN hk
  set a := N ^ (-(1 : ℝ) / k)
  have hN0 : 0 < N := by linarith
  have hh1 : 0 < h + 1 := by linarith
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioc 0 a ∪ Ioc a 1 := by
    intro x hx
    rcases le_or_gt x a with h1 | h1
    · exact Or.inl ⟨hx.1, h1⟩
    · exact Or.inr ⟨h1, hx.2⟩
  refine (lintegral_mono_set hsub).trans ((lintegral_union_le _ _ _).trans (add_le_add ?_ le_rfl))
  calc ∫⁻ x in Ioc 0 a, ENNReal.ofReal (x ^ h) * F (N * x ^ k)
      ≤ ∫⁻ x in Ioc 0 a, ENNReal.ofReal (x ^ h) * ENNReal.ofReal B := by
        refine setLIntegral_mono' measurableSet_Ioc fun x hx => ?_
        gcongr
        exact (hF 0 _ le_rfl (by have := hx.1; positivity)).trans hB
    _ = _ := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_Ioc_zero_rpow ha0.le hh,
          hae, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring_nf

/-- Pointwise bound on the outer piece from the upper half of `F`'s pair. -/
theorem stepG_outer_pt {lam C : ℝ} {j : ℕ} (_hC : 0 ≤ C)
    (hup : ∀ M, 1 ≤ M → F M ≤ ENNReal.ofReal (C * M ^ (-lam) * (1 + Real.log M) ^ j))
    (hk : 1 ≤ k) {N x : ℝ} (hN : 1 ≤ N) (hx : x ∈ Ioc (N ^ (-(1 : ℝ) / k)) 1) :
    ENNReal.ofReal (x ^ h) * F (N * x ^ k) ≤
      ENNReal.ofReal (C * N ^ (-lam) * (1 + Real.log (N * x ^ k)) ^ j *
        x ^ (h - k * lam)) := by
  obtain ⟨ha0, ha1, haN, -⟩ := split_point hN hk
  have hN0 : 0 < N := by linarith
  have hx0 : 0 < x := lt_trans ha0 hx.1
  have hM : 1 ≤ N * x ^ k := by
    rw [← haN]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0.le hx.1.le _) hN0.le
  calc ENNReal.ofReal (x ^ h) * F (N * x ^ k)
      ≤ ENNReal.ofReal (x ^ h) *
          ENNReal.ofReal (C * (N * x ^ k) ^ (-lam) * (1 + Real.log (N * x ^ k)) ^ j) := by
        gcongr; exact hup _ hM
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hx0.le _)]
      congr 1
      rw [Real.mul_rpow hN0.le (by positivity), ← Real.rpow_natCast x (k),
        ← Real.rpow_mul hx0.le, sub_eq_add_neg, Real.rpow_add hx0]
      ring_nf

theorem lintegral_outer_const {a K e : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hK : 0 ≤ K) (he : e ≠ -1) :
    ∫⁻ x in Ioc a 1, ENNReal.ofReal (K * x ^ e) =
      ENNReal.ofReal K * ENNReal.ofReal ((1 - a ^ (e + 1)) / (e + 1)) := by
  simp_rw [ENNReal.ofReal_mul hK]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_Ioc_one_rpow ha ha1 he]

/-- The upper half of a pair, normalized to a nonnegative constant. -/
theorem upper_nonneg {lam : ℝ} {j : ℕ}
    (hup : ∃ C : ℝ, ∀ M, 1 ≤ M → F M ≤ ENNReal.ofReal (C * M ^ (-lam) * (1 + Real.log M) ^ j)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M, 1 ≤ M →
      F M ≤ ENNReal.ofReal (C * M ^ (-lam) * (1 + Real.log M) ^ j) := by
  obtain ⟨C, hC⟩ := hup
  refine ⟨max C 0, le_max_right _ _, fun M hM => (hC M hM).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have : 0 ≤ M ^ (-lam) * (1 + Real.log M) ^ j :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (pow_nonneg (by linarith [Real.log_nonneg hM]) _)
  rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) this

theorem log_bounds_outer {N x : ℝ} (hk : 1 ≤ k) (hN : 1 ≤ N)
    (hx : x ∈ Ioc (N ^ (-(1 : ℝ) / k)) 1) :
    0 ≤ Real.log (N * x ^ k) ∧ Real.log (N * x ^ k) ≤ Real.log N := by
  obtain ⟨ha0, -, haN, -⟩ := split_point hN hk
  have hN0 : 0 < N := by linarith
  have hx0 : 0 < x := lt_trans ha0 hx.1
  constructor
  · apply Real.log_nonneg; rw [← haN]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0.le hx.1.le _) hN0.le
  · apply Real.log_le_log (by positivity)
    exact mul_le_of_le_one_right hN0.le (pow_le_one₀ hx0.le hx.2)

/-- **(U1)** If `λ < μ`: `G(N) ≤ C' N^{-λ} (1+log N)^j`. -/
theorem stepG_upper_lt (hF : ∀ M M', 0 ≤ M → M ≤ M' → F M' ≤ F M) (hh : -1 < h) (hk : 1 ≤ k)
    {B : ℝ} (hB : F 0 ≤ ENNReal.ofReal B) {lam : ℝ} {j : ℕ}
    (hup : ∃ C : ℝ, ∀ M, 1 ≤ M → F M ≤ ENNReal.ofReal (C * M ^ (-lam) * (1 + Real.log M) ^ j))
    (hlt : lam < (h + 1) / k) :
    ∃ C : ℝ, ∀ N, 1 ≤ N →
      stepG F h k N ≤ ENNReal.ofReal (C * N ^ (-lam) * (1 + Real.log N) ^ j) := by
  obtain ⟨C, hC, hC'⟩ := upper_nonneg hup
  have hq : (0 : ℝ) < k := by exact_mod_cast hk
  set e := h - k * lam
  have he : 0 < e + 1 := by
    have := (lt_div_iff₀ hq).mp hlt; simp only [e]; linarith
  have hB' : F 0 ≤ ENNReal.ofReal (max B 0) := hB.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hh1 : 0 < h + 1 := by linarith
  refine ⟨max B 0 / (h + 1) + C / (e + 1), fun N hN => ?_⟩
  obtain ⟨ha0, ha1, -, -⟩ := split_point hN hk
  set a := N ^ (-(1 : ℝ) / k)
  have hN0 : 0 < N := by linarith
  have hL : 1 ≤ (1 + Real.log N) ^ j := one_le_pow₀ (by linarith [Real.log_nonneg hN])
  have hP : 0 ≤ C * N ^ (-lam) * (1 + Real.log N) ^ j := by positivity
  refine (stepG_split_le hF hh hk hB' (le_max_right _ _) hN).trans ?_
  have houter : ∫⁻ x in Ioc a 1, ENNReal.ofReal (x ^ h) * F (N * x ^ k) ≤
      ENNReal.ofReal (C * N ^ (-lam) * (1 + Real.log N) ^ j / (e + 1)) := by
    calc ∫⁻ x in Ioc a 1, ENNReal.ofReal (x ^ h) * F (N * x ^ k)
        ≤ ∫⁻ x in Ioc a 1, ENNReal.ofReal (C * N ^ (-lam) * (1 + Real.log N) ^ j * x ^ e) := by
          refine setLIntegral_mono' measurableSet_Ioc fun x hx => ?_
          refine (stepG_outer_pt hC hC' hk hN hx).trans (ENNReal.ofReal_le_ofReal ?_)
          obtain ⟨l0, l1⟩ := log_bounds_outer hk hN hx
          have hx0 : 0 < x := lt_trans ha0 hx.1
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx0.le _)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ (by linarith) (by linarith) _
      _ ≤ _ := by
          rw [lintegral_outer_const ha0 ha1 hP (by linarith), ← ENNReal.ofReal_mul hP]
          apply ENNReal.ofReal_le_ofReal
          rw [show C * N ^ (-lam) * (1 + Real.log N) ^ j / (e + 1) =
            C * N ^ (-lam) * (1 + Real.log N) ^ j * (1 / (e + 1)) by ring]
          apply mul_le_mul_of_nonneg_left _ hP
          have : 0 ≤ a ^ (e + 1) := Real.rpow_nonneg ha0.le _
          exact div_le_div_of_nonneg_right (by linarith) he.le
  refine (add_le_add le_rfl houter).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hpow : N ^ (-((h + 1) / k)) ≤ N ^ (-lam) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hNl : 0 ≤ N ^ (-lam) := Real.rpow_nonneg hN0.le _
  have h1 : max B 0 / (h + 1) * N ^ (-((h + 1) / k)) ≤
      max B 0 / (h + 1) * (N ^ (-lam) * (1 + Real.log N) ^ j) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc N ^ (-((h + 1) / k)) ≤ N ^ (-lam) := hpow
      _ ≤ N ^ (-lam) * (1 + Real.log N) ^ j := le_mul_of_one_le_right hNl hL
  have h2 : C * N ^ (-lam) * (1 + Real.log N) ^ j / (e + 1) =
      C / (e + 1) * (N ^ (-lam) * (1 + Real.log N) ^ j) := by ring
  rw [h2]; nlinarith

/-- **(U2)** If `λ = μ`: `G(N) ≤ C' N^{-μ} (1+log N)^{j+1}` (one more logarithm). -/
theorem stepG_upper_eq (hF : ∀ M M', 0 ≤ M → M ≤ M' → F M' ≤ F M) (hh : -1 < h) (hk : 1 ≤ k)
    {B : ℝ} (hB : F 0 ≤ ENNReal.ofReal B) {lam : ℝ} {j : ℕ}
    (hup : ∃ C : ℝ, ∀ M, 1 ≤ M → F M ≤ ENNReal.ofReal (C * M ^ (-lam) * (1 + Real.log M) ^ j))
    (heq : lam = (h + 1) / k) :
    ∃ C : ℝ, ∀ N, 1 ≤ N →
      stepG F h k N ≤ ENNReal.ofReal (C * N ^ (-lam) * (1 + Real.log N) ^ (j + 1)) := by
  obtain ⟨C, hC, hC'⟩ := upper_nonneg hup
  have hq : (0 : ℝ) < k := by exact_mod_cast hk
  have he : h - k * lam = -1 := by rw [heq]; field_simp; ring
  have hB' : F 0 ≤ ENNReal.ofReal (max B 0) := hB.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hh1 : 0 < h + 1 := by linarith
  refine ⟨max B 0 / (h + 1) + C, fun N hN => ?_⟩
  obtain ⟨ha0, ha1, -, hae⟩ := split_point hN hk
  set a := N ^ (-(1 : ℝ) / k)
  have hN0 : 0 < N := by linarith
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hL : 1 ≤ (1 + Real.log N) ^ j := one_le_pow₀ (by linarith)
  have hP : 0 ≤ C * N ^ (-lam) * (1 + Real.log N) ^ j := by positivity
  have hloga : Real.log (1 / a) = Real.log N / k := by
    simp only [a]; rw [one_div, Real.log_inv, Real.log_rpow hN0]; ring
  refine (stepG_split_le hF hh hk hB' (le_max_right _ _) hN).trans ?_
  have houter : ∫⁻ x in Ioc a 1, ENNReal.ofReal (x ^ h) * F (N * x ^ k) ≤
      ENNReal.ofReal (C * N ^ (-lam) * (1 + Real.log N) ^ j * (Real.log N / k)) := by
    calc ∫⁻ x in Ioc a 1, ENNReal.ofReal (x ^ h) * F (N * x ^ k)
        ≤ ∫⁻ x in Ioc a 1, ENNReal.ofReal (C * N ^ (-lam) * (1 + Real.log N) ^ j) *
            ENNReal.ofReal (x ^ (-1 : ℝ)) := by
          refine setLIntegral_mono' measurableSet_Ioc fun x hx => ?_
          refine (stepG_outer_pt hC hC' hk hN hx).trans ?_
          rw [he, ← ENNReal.ofReal_mul hP]
          apply ENNReal.ofReal_le_ofReal
          obtain ⟨l0, l1⟩ := log_bounds_outer hk hN hx
          have hx0 : 0 < x := lt_trans ha0 hx.1
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx0.le _)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_Ioc_one_inv ha0 ha1, hloga,
            ← ENNReal.ofReal_mul hP]
  refine (add_le_add le_rfl houter).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← heq]
  have hNl : 0 ≤ N ^ (-lam) := Real.rpow_nonneg hN0.le _
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : 1 ≤ (k : ℝ) := by linarith
  have hlogq : Real.log N / k ≤ 1 + Real.log N := by
    rw [div_le_iff₀ hq]; nlinarith
  have hL1 : (1 + Real.log N) ^ j ≤ (1 + Real.log N) ^ (j + 1) :=
    pow_le_pow_right₀ (by linarith) (Nat.le_succ j)
  have t1 : max B 0 / (h + 1) * N ^ (-lam) ≤ max B 0 / (h + 1) * (N ^ (-lam) *
      (1 + Real.log N) ^ (j + 1)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_mul_of_one_le_right hNl (hL.trans hL1)
  have t2 : C * N ^ (-lam) * (1 + Real.log N) ^ j * (Real.log N / k) ≤
      C * (N ^ (-lam) * (1 + Real.log N) ^ (j + 1)) := by
    rw [pow_succ]
    have : 0 ≤ C * N ^ (-lam) * (1 + Real.log N) ^ j := hP
    calc C * N ^ (-lam) * (1 + Real.log N) ^ j * (Real.log N / k)
        ≤ C * N ^ (-lam) * (1 + Real.log N) ^ j * (1 + Real.log N) :=
          mul_le_mul_of_nonneg_left hlogq this
      _ = _ := by ring
  nlinarith

/-- **(U3)** If `μ < λ`: `G(N) ≤ C' N^{-μ}` (no logarithm survives). -/
theorem stepG_upper_gt (hF : ∀ M M', 0 ≤ M → M ≤ M' → F M' ≤ F M) (hh : -1 < h) (hk : 1 ≤ k)
    {B : ℝ} (hB : F 0 ≤ ENNReal.ofReal B) {lam : ℝ} {j : ℕ}
    (hup : ∃ C : ℝ, ∀ M, 1 ≤ M → F M ≤ ENNReal.ofReal (C * M ^ (-lam) * (1 + Real.log M) ^ j))
    (hgt : (h + 1) / k < lam) :
    ∃ C : ℝ, ∀ N, 1 ≤ N →
      stepG F h k N ≤ ENNReal.ofReal (C * N ^ (-((h + 1) / k)) * (1 + Real.log N) ^ 0) := by
  obtain ⟨C, hC, hC'⟩ := upper_nonneg hup
  have hq : (0 : ℝ) < k := by exact_mod_cast hk
  set μ := (h + 1) / k
  set ε := (lam - μ) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  obtain ⟨D, hD, hDb⟩ := one_add_log_pow_le hε j
  set e := h - k * lam + k * ε
  have he1 : e + 1 = -(k * ε) := by
    simp only [e, ε, μ]; field_simp; ring
  have he : e ≠ -1 := by intro h'; rw [h'] at he1; have := mul_pos hq hε; linarith
  have hB' : F 0 ≤ ENNReal.ofReal (max B 0) := hB.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hh1 : 0 < h + 1 := by linarith
  refine ⟨max B 0 / (h + 1) + C * D / (k * ε), fun N hN => ?_⟩
  obtain ⟨ha0, ha1, -, hae⟩ := split_point hN hk
  set a := N ^ (-(1 : ℝ) / k)
  have hN0 : 0 < N := by linarith
  have hP : 0 ≤ C * D * N ^ (-lam + ε) := by positivity
  refine (stepG_split_le hF hh hk hB' (le_max_right _ _) hN).trans ?_
  have houter : ∫⁻ x in Ioc a 1, ENNReal.ofReal (x ^ h) * F (N * x ^ k) ≤
      ENNReal.ofReal (C * D / (k * ε) * N ^ (-μ)) := by
    calc ∫⁻ x in Ioc a 1, ENNReal.ofReal (x ^ h) * F (N * x ^ k)
        ≤ ∫⁻ x in Ioc a 1, ENNReal.ofReal (C * D * N ^ (-lam + ε) * x ^ e) := by
          refine setLIntegral_mono' measurableSet_Ioc fun x hx => ?_
          refine (stepG_outer_pt hC hC' hk hN hx).trans (ENNReal.ofReal_le_ofReal ?_)
          obtain ⟨l0, -⟩ := log_bounds_outer hk hN hx
          have hx0 : 0 < x := lt_trans ha0 hx.1
          have hM1 : 1 ≤ N * x ^ k := by
            have := Real.add_one_le_exp (Real.log (N * x ^ k))
            rw [Real.exp_log (by positivity)] at this; linarith
          have hlog := hDb _ hM1
          have hMε : (N * x ^ k) ^ ε = N ^ ε * x ^ (k * ε) := by
            rw [Real.mul_rpow hN0.le (by positivity), ← Real.rpow_natCast x (k),
              ← Real.rpow_mul hx0.le]
          rw [hMε] at hlog
          have hxe : x ^ (h - k * lam) * x ^ (k * ε) = x ^ e := by
            rw [← Real.rpow_add hx0]
          have hNe : N ^ (-lam) * N ^ ε = N ^ (-lam + ε) := by rw [← Real.rpow_add hN0]
          calc C * N ^ (-lam) * (1 + Real.log (N * x ^ k)) ^ j * x ^ (h - k * lam)
              ≤ C * N ^ (-lam) * (D * (N ^ ε * x ^ (k * ε))) * x ^ (h - k * lam) := by
                gcongr
            _ = C * D * N ^ (-lam + ε) * x ^ e := by rw [← hxe, ← hNe]; ring
      _ ≤ _ := by
          rw [lintegral_outer_const ha0 ha1 hP he, ← ENNReal.ofReal_mul hP]
          apply ENNReal.ofReal_le_ofReal
          have hae1 : a ^ (e + 1) = N ^ ε := by
            rw [hae, he1]; congr 1; field_simp
          rw [hae1, he1]
          have hNε : 0 ≤ N ^ ε := Real.rpow_nonneg hN0.le _
          have hden : 0 < k * ε := mul_pos hq hε
          have e2 : N ^ (-lam + ε) * N ^ ε = N ^ (-μ) := by
            rw [← Real.rpow_add hN0]; congr 1; simp only [ε]; ring
          rw [show (1 - N ^ ε) / -(k * ε) = (N ^ ε - 1) / (k * ε) by
            field_simp; ring]
          calc C * D * N ^ (-lam + ε) * ((N ^ ε - 1) / (k * ε))
              ≤ C * D * N ^ (-lam + ε) * (N ^ ε / (k * ε)) := by
                apply mul_le_mul_of_nonneg_left _ hP
                exact div_le_div_of_nonneg_right (by linarith) hden.le
            _ = C * D / (k * ε) * (N ^ (-lam + ε) * N ^ ε) := by ring
            _ = _ := by rw [e2]
  refine (add_le_add le_rfl houter).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  simp only [pow_zero, mul_one]
  apply le_of_eq; ring

theorem rpow_h_ge {h x : ℝ} (hx : x ∈ Ioc (1 / 2 : ℝ) 1) : min 1 ((1 / 2 : ℝ) ^ h) ≤ x ^ h := by
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  rcases le_total 0 h with hh | hh
  · exact (min_le_right _ _).trans (Real.rpow_le_rpow (by norm_num) hx.1.le hh)
  · exact (min_le_left _ _).trans (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx0 hx.2 hh)

/-- **(L2)** From the lower half of `F`'s pair: `G(N) ≥ c' N^{-λ} (log N)^j` for large `N`. -/
theorem stepG_lower_lam (_hk : 1 ≤ k) {lam : ℝ} (hlam : 0 ≤ lam) {j : ℕ}
    (hlow : ∃ c : ℝ, 0 < c ∧ ∃ M₀ : ℝ, ∀ M, M₀ ≤ M →
      ENNReal.ofReal (c * M ^ (-lam) * Real.log M ^ j) ≤ F M) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N, N₀ ≤ N →
      ENNReal.ofReal (c * N ^ (-lam) * Real.log N ^ j) ≤ stepG F h k N := by
  obtain ⟨c, hc, M₀, hM₀⟩ := hlow
  set w := min 1 ((1 / 2 : ℝ) ^ h)
  have hw : 0 < w := lt_min one_pos (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨1 / 2 * w * c * (1 / 2) ^ j, by positivity,
    max (16 ^ k) (4 ^ k * max M₀ 1), fun N hN => ?_⟩
  have hN16 : (16 : ℝ) ^ k ≤ N := (le_max_left _ _).trans hN
  have hNM : 4 ^ k * max M₀ 1 ≤ N := (le_max_right _ _).trans hN
  have h4 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have hN1 : 1 ≤ N := le_trans (by nlinarith [le_max_right M₀ 1]) hNM
  have hN0 : 0 < N := by linarith
  have hlogN : 4 * k * Real.log 2 ≤ Real.log N := by
    have := Real.log_le_log (by positivity) hN16
    rw [Real.log_pow, show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at this
    push_cast at this; linarith
  have hpt : ∀ x ∈ Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (w * (c * N ^ (-lam) * (1 / 2) ^ j *
      Real.log N ^ j)) ≤ ENNReal.ofReal (x ^ h) * F (N * x ^ k) := by
    intro x hx
    have hx0 : 0 < x := lt_trans (by norm_num) hx.1
    have hxq : (1 / 4 : ℝ) ^ k ≤ x ^ k := by
      exact pow_le_pow_left₀ (by positivity) (by linarith [hx.1]) _
    have hxq1 : x ^ k ≤ 1 := pow_le_one₀ hx0.le hx.2
    set M := N * x ^ k
    have hM0 : 0 < M := by positivity
    have hMN : M ≤ N := mul_le_of_le_one_right hN0.le hxq1
    have hMlow : N / 4 ^ k ≤ M := by
      rw [div_le_iff₀ (by positivity)]
      calc N = N * (4 ^ k * (1 / 4) ^ k) := by rw [← mul_pow]; norm_num
        _ ≤ N * (4 ^ k * x ^ k) := by gcongr
        _ = M * 4 ^ k := by simp only [M]; ring
    have hMM₀ : M₀ ≤ M := by
      refine le_trans ?_ hMlow
      rw [le_div_iff₀ (by positivity)]; nlinarith [le_max_left M₀ 1]
    have hlogM : Real.log N / 2 ≤ Real.log M := by
      have := Real.log_le_log (by positivity) hMlow
      rw [Real.log_div hN0.ne' (by positivity), Real.log_pow,
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at this
      push_cast at this; linarith
    have hrp : N ^ (-lam) ≤ M ^ (-lam) := Real.rpow_le_rpow_of_nonpos hM0 hMN (by linarith)
    have hlN : 0 ≤ Real.log N := Real.log_nonneg hN1
    have hFM := hM₀ M hMM₀
    have : w * (c * N ^ (-lam) * (1 / 2) ^ j * Real.log N ^ j) ≤
        x ^ h * (c * M ^ (-lam) * Real.log M ^ j) := by
      apply mul_le_mul (rpow_h_ge hx) _ (by positivity) (Real.rpow_nonneg hx0.le _)
      have hl : (1 / 2 : ℝ) ^ j * Real.log N ^ j ≤ Real.log M ^ j := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
      calc c * N ^ (-lam) * (1 / 2) ^ j * Real.log N ^ j
          = c * N ^ (-lam) * ((1 / 2) ^ j * Real.log N ^ j) := by ring
        _ ≤ c * M ^ (-lam) * Real.log M ^ j :=
          mul_le_mul (mul_le_mul_of_nonneg_left hrp hc.le) hl (by positivity)
            (by positivity)
    refine (ENNReal.ofReal_le_ofReal this).trans ?_
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hx0.le _)]
    gcongr
  calc ENNReal.ofReal (1 / 2 * w * c * (1 / 2) ^ j * N ^ (-lam) * Real.log N ^ j)
      = ∫⁻ _ in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (w * (c * N ^ (-lam) * (1 / 2) ^ j *
          Real.log N ^ j)) := by
        rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul (by
          have := Real.log_nonneg hN1
          positivity)]
        congr 1; ring
    _ ≤ ∫⁻ x in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (x ^ h) * F (N * x ^ k) :=
        setLIntegral_mono' measurableSet_Ioc hpt
    _ ≤ stepG F h k N := lintegral_mono_set (Ioc_subset_Ioc_left (by norm_num))

/-- **(L3)** If `λ = μ`: `G(N) ≥ c' N^{-μ} (log N)^{j+1}` for large `N`. -/
theorem stepG_lower_eq (hk : 1 ≤ k) {lam : ℝ} {j : ℕ} (heq : lam = (h + 1) / k)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∃ M₀ : ℝ, ∀ M, M₀ ≤ M →
      ENNReal.ofReal (c * M ^ (-lam) * Real.log M ^ j) ≤ F M) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N, N₀ ≤ N →
      ENNReal.ofReal (c * N ^ (-lam) * Real.log N ^ (j + 1)) ≤ stepG F h k N := by
  obtain ⟨c, hc, M₀, hM₀⟩ := hlow
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq : (0 : ℝ) < k := by linarith
  set M₁ := max M₀ 1
  refine ⟨c * (1 / 2) ^ j / (2 * k), by positivity, M₁ ^ 2, fun N hN => ?_⟩
  have hM1 : 1 ≤ M₁ := le_max_right _ _
  have hN1 : 1 ≤ N := le_trans (one_le_pow₀ hM1) hN
  have hN0 : 0 < N := by linarith
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN1
  set a := N ^ (-(1 : ℝ) / (2 * k))
  have ha0 : 0 < a := Real.rpow_pos_of_pos hN0 _
  have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1
    (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
  have hloga : Real.log a = -(Real.log N / (2 * k)) := by
    simp only [a]; rw [Real.log_rpow hN0]; ring
  have hsqrt : N ^ ((1 : ℝ) / 2) ≥ M₁ := by
    have := Real.rpow_le_rpow (by positivity) hN (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)] at this
    norm_num at this; exact this
  have he : h - k * lam = -1 := by rw [heq]; field_simp; ring
  have hpt : ∀ x ∈ Ioc a 1, ENNReal.ofReal (c * (1 / 2) ^ j * N ^ (-lam) * Real.log N ^ j *
      x ^ (-1 : ℝ)) ≤ ENNReal.ofReal (x ^ h) * F (N * x ^ k) := by
    intro x hx
    have hx0 : 0 < x := lt_trans ha0 hx.1
    set M := N * x ^ k
    have hM0 : 0 < M := by positivity
    have hlogM : Real.log M = Real.log N + k * Real.log x := by
      simp only [M]; rw [Real.log_mul hN0.ne' (by positivity), Real.log_pow]
    have hlx : Real.log a ≤ Real.log x := Real.log_le_log ha0 hx.1.le
    have hlogM2 : Real.log N / 2 ≤ Real.log M := by
      rw [hlogM, hloga] at *
      have : k * (-(Real.log N / (2 * k))) = -(Real.log N / 2) := by field_simp
      nlinarith
    have hMM : M₀ ≤ M := by
      refine (le_max_left M₀ 1).trans (hsqrt.le.trans ?_)
      rw [← Real.exp_log hM0, ← Real.exp_log (Real.rpow_pos_of_pos hN0 _), Real.log_rpow hN0]
      exact Real.exp_le_exp.mpr (by linarith)
    have hFM := hM₀ M hMM
    have hMp : M ^ (-lam) = N ^ (-lam) * x ^ (-(k * lam)) := by
      simp only [M]
      rw [Real.mul_rpow hN0.le (by positivity), ← Real.rpow_natCast x (k),
        ← Real.rpow_mul hx0.le]; try (ring_nf)
    have hxx : x ^ h * x ^ (-(k * lam)) = x ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hx0, ← he]; ring_nf
    calc ENNReal.ofReal (c * (1 / 2) ^ j * N ^ (-lam) * Real.log N ^ j * x ^ (-1 : ℝ))
        ≤ ENNReal.ofReal (x ^ h * (c * M ^ (-lam) * Real.log M ^ j)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hMp]
          have hl : (1 / 2 : ℝ) ^ j * Real.log N ^ j ≤ Real.log M ^ j := by
            rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
          have hpos : 0 ≤ c * N ^ (-lam) * x ^ (-1 : ℝ) := by positivity
          calc c * (1 / 2) ^ j * N ^ (-lam) * Real.log N ^ j * x ^ (-1 : ℝ)
              = (c * N ^ (-lam) * x ^ (-1 : ℝ)) * ((1 / 2) ^ j * Real.log N ^ j) := by ring
            _ ≤ (c * N ^ (-lam) * x ^ (-1 : ℝ)) * Real.log M ^ j :=
                mul_le_mul_of_nonneg_left hl hpos
            _ = _ := by rw [← hxx]; ring
      _ ≤ _ := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hx0.le _)]; gcongr
  have hPos : 0 ≤ c * (1 / 2) ^ j * N ^ (-lam) * Real.log N ^ j := by positivity
  calc ENNReal.ofReal (c * (1 / 2) ^ j / (2 * k) * N ^ (-lam) * Real.log N ^ (j + 1))
      = ENNReal.ofReal (c * (1 / 2) ^ j * N ^ (-lam) * Real.log N ^ j) *
          ENNReal.ofReal (Real.log (1 / a)) := by
        have hl1 : Real.log (1 / a) = Real.log N / (2 * k) := by
          rw [Real.log_div one_ne_zero ha0.ne', Real.log_one, hloga]; ring
        rw [← ENNReal.ofReal_mul hPos, hl1]
        congr 1; field_simp; ring
    _ = ∫⁻ x in Ioc a 1, ENNReal.ofReal (c * (1 / 2) ^ j * N ^ (-lam) * Real.log N ^ j *
          x ^ (-1 : ℝ)) := by
        simp_rw [ENNReal.ofReal_mul hPos]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_Ioc_one_inv ha0 ha1]
    _ ≤ ∫⁻ x in Ioc a 1, ENNReal.ofReal (x ^ h) * F (N * x ^ k) :=
        setLIntegral_mono' measurableSet_Ioc hpt
    _ ≤ stepG F h k N := lintegral_mono_set (Ioc_subset_Ioc_left ha0.le)

/-! ### The step on `NCBound` -/

theorem NCBound.common {lam : ℝ} {m : ℕ} (hF : NCBound F lam m) (hh : -1 < h) (hk : 1 ≤ k) :
    (∀ M M', 0 ≤ M → M ≤ M' → stepG F h k M' ≤ stepG F h k M) ∧
    (∃ B : ℝ, stepG F h k 0 ≤ ENNReal.ofReal B) ∧
    (∃ b : ℝ, 0 < b ∧ ENNReal.ofReal b ≤ stepG F h k 1) := by
  obtain ⟨hmono, ⟨B, hB⟩, ⟨b, hb, hb1⟩, -, -⟩ := hF
  have hh1 : 0 < h + 1 := by linarith
  refine ⟨fun M M' hM hMM => stepG_mono hmono hM hMM, ⟨B / (h + 1), stepG_zero_le hh hB⟩,
    ⟨b / (h + 1), by positivity, ?_⟩⟩
  have := stepG_lower_mu hmono hh hk hb hb1 le_rfl
  rwa [Real.one_rpow, mul_one] at this

/-- Step, case `μ > λ`: the pair `(λ, m)` is unchanged. -/
theorem NCBound.step_lt {lam : ℝ} {m : ℕ} (hF : NCBound F lam m) (hlam : 0 ≤ lam)
    (hh : -1 < h) (hk : 1 ≤ k) (hlt : lam < (h + 1) / k) :
    NCBound (stepG F h k) lam m := by
  obtain ⟨c1, c2, c3⟩ := hF.common hh hk
  obtain ⟨hmono, ⟨B, hB⟩, -, hup, hlow⟩ := hF
  obtain ⟨C, hC⟩ := stepG_upper_lt hmono hh hk hB hup hlt
  exact ⟨c1, c2, c3, ⟨C, hC⟩, stepG_lower_lam hk hlam hlow⟩

/-- Step, case `μ = λ`: one more logarithm, `(λ, m+1)`. -/
theorem NCBound.step_eq {lam : ℝ} {m : ℕ} (hF : NCBound F lam m) (hm : 1 ≤ m)
    (hh : -1 < h) (hk : 1 ≤ k) (heq : lam = (h + 1) / k) :
    NCBound (stepG F h k) lam (m + 1) := by
  obtain ⟨c1, c2, c3⟩ := hF.common hh hk
  obtain ⟨hmono, ⟨B, hB⟩, -, hup, hlow⟩ := hF
  obtain ⟨C, hC⟩ := stepG_upper_eq hmono hh hk hB hup heq
  obtain ⟨c, hc, N₀, hlo⟩ := stepG_lower_eq (h := h) hk heq hlow
  have e : m + 1 - 1 = m - 1 + 1 := by omega
  refine ⟨c1, c2, c3, ⟨C, fun N hN => ?_⟩, ⟨c, hc, N₀, fun N hN => ?_⟩⟩
  · rw [e]; exact hC N hN
  · rw [e]; exact hlo N hN

/-- Step, case `μ < λ`: the new coordinate dominates, `(μ, 1)`. -/
theorem NCBound.step_gt_of_upper (hmono : ∀ M M', 0 ≤ M → M ≤ M' → F M' ≤ F M)
    {B : ℝ} (hB : F 0 ≤ ENNReal.ofReal B) {b : ℝ} (hb : 0 < b) (hb1 : ENNReal.ofReal b ≤ F 1)
    {lam : ℝ} {j : ℕ}
    (hup : ∃ C : ℝ, ∀ M, 1 ≤ M → F M ≤ ENNReal.ofReal (C * M ^ (-lam) * (1 + Real.log M) ^ j))
    (hh : -1 < h) (hk : 1 ≤ k) (hgt : (h + 1) / k < lam) :
    NCBound (stepG F h k) ((h + 1) / k) 1 := by
  have hh1 : 0 < h + 1 := by linarith
  have hlow := fun N (hN : 1 ≤ N) => stepG_lower_mu hmono hh hk hb hb1 hN
  refine ⟨fun M M' hM hMM => stepG_mono hmono hM hMM, ⟨B / (h + 1), stepG_zero_le hh hB⟩,
    ⟨b / (h + 1), by positivity, ?_⟩, stepG_upper_gt hmono hh hk hB hup hgt,
    ⟨b / (h + 1), by positivity, 1, fun N hN => ?_⟩⟩
  · have := hlow 1 le_rfl; rwa [Real.one_rpow, mul_one] at this
  · simpa using hlow N hN

theorem NCBound.step_gt {lam : ℝ} {m : ℕ} (hF : NCBound F lam m)
    (hh : -1 < h) (hk : 1 ≤ k) (hgt : (h + 1) / k < lam) :
    NCBound (stepG F h k) ((h + 1) / k) 1 := by
  obtain ⟨hmono, ⟨B, hB⟩, ⟨b, hb, hb1⟩, hup, -⟩ := hF
  exact NCBound.step_gt_of_upper hmono hB hb hb1 hup hh hk hgt

end Step

/-- The base of the induction: `e^{-M}` has every upper exponent. -/
theorem exp_neg_upper {lam : ℝ} (_hlam : 0 ≤ lam) :
    ∃ C : ℝ, ∀ M, 1 ≤ M → ENNReal.ofReal (Real.exp (-M)) ≤
      ENNReal.ofReal (C * M ^ (-lam) * (1 + Real.log M) ^ 0) := by
  obtain ⟨n, hn⟩ := exists_nat_ge lam
  refine ⟨n.factorial, fun M hM => ENNReal.ofReal_le_ofReal ?_⟩
  have hM0 : 0 < M := by linarith
  have h1 := Real.pow_div_factorial_le_exp M hM0.le n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h2 : M ^ (-lam) ≥ M ^ (-(n : ℝ)) := Real.rpow_le_rpow_of_exponent_le hM (by linarith)
  have h3 : M ^ (-(n : ℝ)) = (M ^ n)⁻¹ := by rw [Real.rpow_neg hM0.le, Real.rpow_natCast]
  rw [pow_zero, mul_one, Real.exp_neg]
  have hMn : 0 < M ^ n := pow_pos hM0 n
  have : (Real.exp M)⁻¹ ≤ n.factorial * (M ^ n)⁻¹ := by
    rw [inv_le_comm₀ (Real.exp_pos _) (by positivity), mul_inv, inv_inv]
    calc (n.factorial : ℝ)⁻¹ * M ^ n = M ^ n / n.factorial := by ring
      _ ≤ _ := h1
  calc (Real.exp M)⁻¹ ≤ n.factorial * (M ^ n)⁻¹ := this
    _ ≤ n.factorial * M ^ (-lam) := by rw [← h3]; exact mul_le_mul_of_nonneg_left h2 hf.le

/-- **Base case** (one variable): `∫₀¹ x^h e^{-N x^{k}} dx` has bounds `((h+1)/(k), 1)`. -/
theorem NCBound.base {h : ℝ} {k : ℕ} (hh : -1 < h) (hk : 1 ≤ k) :
    NCBound (stepG (fun M => ENNReal.ofReal (Real.exp (-M))) h k) ((h + 1) / k) 1 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hh1 : 0 < h + 1 := by linarith
  have hpos : 0 ≤ (h + 1) / k + 1 := by positivity
  refine NCBound.step_gt_of_upper (B := 1) (b := Real.exp (-1)) (j := 0)
    (lam := (h + 1) / k + 1) (fun M M' hM hMM => ?_) (by simp) (Real.exp_pos _) le_rfl
    (exp_neg_upper hpos) hh hk (by linarith)
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))

end SLT.NC
