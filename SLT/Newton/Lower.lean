/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Laplace.Volume

/-!
# Newton-polyhedron RLCTs, the easy half (brief 01, stage N1)

Exponents `Γ ⊂ ℝ≥0^d` (a `Finset`), monomials `|w|^α = ∏ |w_i|^{α_i}` (real powers), the unit box
`[0,1]^d` with Lebesgue measure.

**Newton distance, max–min form.** A *Newton certificate* for `t` is a weight vector `u` in the
standard simplex (`u ≥ 0`, `∑ u = 1`) with `t ≤ ⟨α, u⟩` for every `α ∈ Γ`. Then
`newtonDist Γ = sup { t | some u certifies t } = max_{u ∈ Δ} min_{α ∈ Γ} ⟨α, u⟩`.
This is the brief's second (minimax) formula for `t* = min { t | t·𝟙 ∈ conv Γ + ℝ≥0^d }`. The
LP-duality equivalence with the polyhedral formula is **not** formalised here; nothing in N1 needs
it.

* `monomial_le_of_mem_box`: on the anisotropic box `∏ [0, ε^{u_i}]`, `|w|^α ≤ ε^t`.
* `newton_laplaceLower`: if `K ≤ C ∑_{α ∈ Γ} |w|^α` on `[0,1]^d` and `u` certifies `t > 0`, then
  `Z(N) ≥ c N^{-1/t}`, i.e. `LaplaceLower Z (1/t) 1`.
* `newton_lambda_le`: hence any Laplace upper pair `(λ, m)` of `Z` has `λ ≤ 1/newtonDist Γ`.
* Sanity checks: `newtonDist` of the brief's table, `{2k}` (`d = 1`), `{(2,2)}`, `{(2,0),(0,2)}`,
  `{(2,0)}` (`d = 2`), is `2k, 2, 1, 2`.
-/

@[expose] public section

namespace SLT.Newton

open MeasureTheory Filter Real Set
open scoped ENNReal

variable {d : ℕ}

/-- The monomial `|w|^α = ∏ |w_i|^{α_i}`. -/
noncomputable def monomial (α w : Fin d → ℝ) : ℝ := ∏ i, |w i| ^ α i

/-- `u` (in the standard simplex) certifies `t ≤ ⟨α, u⟩` for every exponent `α ∈ Γ`. -/
def IsNewtonCert (Γ : Finset (Fin d → ℝ)) (t : ℝ) (u : Fin d → ℝ) : Prop :=
  (∀ i, 0 ≤ u i) ∧ ∑ i, u i = 1 ∧ ∀ α ∈ Γ, t ≤ ∑ i, α i * u i

/-- The Newton distance, max–min form: `t* = max_{u ∈ Δ} min_{α ∈ Γ} ⟨α, u⟩`. -/
noncomputable def newtonDist (Γ : Finset (Fin d → ℝ)) : ℝ :=
  sSup {t | ∃ u, IsNewtonCert Γ t u}

/-- A certificate for `t'` certifies every `t ≤ t'`. -/
theorem IsNewtonCert.mono {Γ : Finset (Fin d → ℝ)} {t t' : ℝ} {u : Fin d → ℝ}
    (h : IsNewtonCert Γ t' u) (htt : t ≤ t') : IsNewtonCert Γ t u :=
  ⟨h.1, h.2.1, fun α hα => htt.trans (h.2.2 α hα)⟩

/-- Monomials `|w|^α` are nonnegative. -/
theorem monomial_nonneg (α w : Fin d → ℝ) : 0 ≤ monomial α w :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _

/-- On the anisotropic box `∏ [0, ε^{u_i}]`, `|w|^α ≤ ε^{⟨α,u⟩} ≤ ε^t`. -/
theorem monomial_le_of_mem_box {α u w : Fin d → ℝ} (hα : ∀ i, 0 ≤ α i) {ε t : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (ht : t ≤ ∑ i, α i * u i) (hw : w ∈ Icc (0 : Fin d → ℝ) fun i => ε ^ u i) :
    monomial α w ≤ ε ^ t := by
  calc monomial α w ≤ ∏ i, (ε ^ u i) ^ α i := by
        refine Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg (abs_nonneg _) _) fun i _ => ?_
        rw [abs_of_nonneg (hw.1 i)]
        exact Real.rpow_le_rpow (hw.1 i) (hw.2 i) (hα i)
    _ = ε ^ ∑ i, α i * u i := by
        rw [Real.rpow_sum_of_pos hε]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Real.rpow_mul hε.le, mul_comm]
    _ ≤ ε ^ t := Real.rpow_le_rpow_of_exponent_ge hε hε1 ht

/-- The anisotropic box `∏ [0, ε^{u_i}]` with `Σ u_i = 1` has volume `ε` (N1). -/
theorem volume_box {u : Fin d → ℝ} (hu1 : ∑ i, u i = 1) {ε : ℝ} (hε : 0 < ε) :
    volume (Icc (0 : Fin d → ℝ) fun i => ε ^ u i) = ENNReal.ofReal ε := by
  rw [Real.volume_Icc_pi]
  simp only [Pi.zero_apply, sub_zero]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.rpow_pos_of_pos hε _).le),
    ← Real.rpow_sum_of_pos hε, hu1, Real.rpow_one]

/-- **N1, Laplace lower bound**: if `K ≤ C ∑_{α ∈ Γ} |w|^α` on `[0,1]^d` and `u` certifies
`t > 0`, then `Z(N) = ∫_{[0,1]^d} e^{-N K} ≥ c N^{-1/t}` for large `N`. -/
theorem newton_laplaceLower {Γ : Finset (Fin d → ℝ)} (hΓ : ∀ α ∈ Γ, ∀ i, 0 ≤ α i) {t : ℝ}
    (ht : 0 < t) {u : Fin d → ℝ} (hu : IsNewtonCert Γ t u) {K : (Fin d → ℝ) → ℝ}
    (hK : Measurable K) {C : ℝ}
    (hKle : ∀ w ∈ Icc (0 : Fin d → ℝ) 1, K w ≤ C * ∑ α ∈ Γ, monomial α w) :
    LaplaceLower (Z (volume.restrict (Icc (0 : Fin d → ℝ) 1)) K) t⁻¹ 1 := by
  obtain ⟨hu0, hu1, hut⟩ := hu
  set C' : ℝ := |C| * Γ.card + 1
  have hC'1 : 1 ≤ C' := by have : 0 ≤ |C| * Γ.card := by positivity
                           linarith
  have hC' : 0 < C' := by linarith
  refine laplaceLower_of_volume hK (c := (C' ^ t⁻¹)⁻¹) (t₀ := 1)
    (inv_pos.mpr (Real.rpow_pos_of_pos hC' _)) one_pos fun s hs hs1 => ?_
  set ε : ℝ := (s / C') ^ t⁻¹
  have hsC : 0 < s / C' := div_pos hs hC'
  have hε : 0 < ε := Real.rpow_pos_of_pos hsC _
  have hε1 : ε ≤ 1 :=
    Real.rpow_le_one hsC.le (by rw [div_le_one hC']; linarith) (inv_pos.mpr ht).le
  have hεt : ε ^ t = s / C' := Real.rpow_inv_rpow hsC.le ht.ne'
  set B : Set (Fin d → ℝ) := Icc 0 fun i => ε ^ u i
  have hB : B ⊆ Icc 0 1 := fun w hw =>
    ⟨hw.1, fun i => (hw.2 i).trans (Real.rpow_le_one hε.le hε1 (hu0 i))⟩
  have hBK : B ⊆ {w | K w ≤ s} := by
    intro w hw
    have hsum : ∑ α ∈ Γ, monomial α w ≤ Γ.card * ε ^ t := by
      have := Finset.sum_le_card_nsmul Γ (fun α => monomial α w) (ε ^ t)
        fun α hα => monomial_le_of_mem_box (hΓ α hα) hε hε1 (hut α hα) hw
      simpa only [nsmul_eq_mul] using this
    have hS := Finset.sum_nonneg fun α (_ : α ∈ Γ) => monomial_nonneg α w
    have hpow : 0 ≤ ε ^ t := (Real.rpow_pos_of_pos hε _).le
    calc K w ≤ C * ∑ α ∈ Γ, monomial α w := hKle w (hB hw)
      _ ≤ |C| * ∑ α ∈ Γ, monomial α w := mul_le_mul_of_nonneg_right (le_abs_self C) hS
      _ ≤ |C| * (Γ.card * ε ^ t) := mul_le_mul_of_nonneg_left hsum (abs_nonneg C)
      _ ≤ C' * ε ^ t := by nlinarith [abs_nonneg C]
      _ = s := by rw [hεt]; field_simp
  have hVB : volume.restrict (Icc (0 : Fin d → ℝ) 1) B = ENNReal.ofReal ε := by
    rw [Measure.restrict_apply measurableSet_Icc, inter_eq_left.mpr hB, volume_box hu1 hε]
  calc ENNReal.ofReal ((C' ^ t⁻¹)⁻¹ * s ^ t⁻¹ * Real.log (1 / s) ^ (1 - 1))
        = ENNReal.ofReal ε := by
          congr 1
          simp only [Nat.sub_self, pow_zero, mul_one, ε]
          rw [Real.div_rpow hs.le hC'.le]
          ring
    _ = volume.restrict (Icc (0 : Fin d → ℝ) 1) B := hVB.symm
    _ ≤ V (volume.restrict (Icc (0 : Fin d → ℝ) 1)) K s := measure_mono hBK

/-- **N1, the easy half**: if `K ≤ C ∑_{α ∈ Γ} |w|^α` on `[0,1]^d` and `t* = newtonDist Γ > 0`,
then every Laplace upper pair `(λ, m)` of `Z` has `λ ≤ 1/t*`. In particular the learning
coefficient of `K` on the box is at most `1/t*`. -/
theorem newton_lambda_le {Γ : Finset (Fin d → ℝ)} (hΓ : ∀ α ∈ Γ, ∀ i, 0 ≤ α i)
    (hd : 0 < newtonDist Γ) {K : (Fin d → ℝ) → ℝ} (hK : Measurable K) {C : ℝ}
    (hKle : ∀ w ∈ Icc (0 : Fin d → ℝ) 1, K w ≤ C * ∑ α ∈ Γ, monomial α w) {lam : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hup : LaplaceUpper (Z (volume.restrict (Icc (0 : Fin d → ℝ) 1)) K) lam m) :
    lam ≤ (newtonDist Γ)⁻¹ := by
  have hne : {t | ∃ u, IsNewtonCert Γ t u}.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [newtonDist, h, Real.sSup_empty] at hd
    exact lt_irrefl _ hd
  -- every `t ∈ (0, t*)` gives `λ ≤ 1/t`
  have key : ∀ t, 0 < t → t < newtonDist Γ → lam ≤ t⁻¹ := by
    intro t ht htd
    obtain ⟨t', ⟨u, hu⟩, htt⟩ := exists_lt_of_lt_csSup hne htd
    have hl := newton_laplaceLower hΓ ht (hu.mono htt.le) hK hKle
    rcases dominates_of_lower_upper hm hl hup with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  by_contra hlt
  push Not at hlt
  have hlam : 0 < lam := lt_trans (inv_pos.mpr hd) hlt
  have h1 : lam⁻¹ < newtonDist Γ := by
    rw [inv_lt_comm₀ hlam hd]; exact hlt
  obtain ⟨t, h2, h3⟩ := exists_between h1
  have ht : 0 < t := lt_trans (inv_pos.mpr hlam) h2
  have := key t ht h3
  rw [le_inv_comm₀ hlam ht] at this
  linarith

/-- `newtonDist` from a certificate and a matching upper bound. -/
theorem newtonDist_eq {Γ : Finset (Fin d → ℝ)} {t : ℝ} {u : Fin d → ℝ} (hu : IsNewtonCert Γ t u)
    (hub : ∀ t' u', IsNewtonCert Γ t' u' → t' ≤ t) : newtonDist Γ = t :=
  IsGreatest.csSup_eq ⟨⟨u, hu⟩, fun t' ⟨u', hu'⟩ => hub t' u' hu'⟩

/-! ### Sanity checks (the brief's table, `t*` column) -/

/-- `|w|^{2k}`, `d = 1`: `t* = 2k`. -/
theorem newtonDist_single (k : ℝ) : newtonDist ({fun _ => 2 * k} : Finset (Fin 1 → ℝ)) = 2 * k := by
  refine newtonDist_eq (u := fun _ => 1) ⟨fun _ => zero_le_one, by simp, by simp⟩ ?_
  rintro t' u' ⟨-, h1, h2⟩
  have := h2 _ (Finset.mem_singleton_self _)
  simp only [Fin.sum_univ_one] at h1 this
  rw [h1, mul_one] at this; exact this

/-- `x² y²`: `t* = 2`. -/
theorem newtonDist_xy : newtonDist ({![2, 2]} : Finset (Fin 2 → ℝ)) = 2 := by
  refine newtonDist_eq (u := ![1 / 2, 1 / 2]) ⟨fun i => by fin_cases i <;> norm_num,
    by simp [Fin.sum_univ_two]; norm_num, by simp [Fin.sum_univ_two]; norm_num⟩ ?_
  rintro t' u' ⟨-, h1, h2⟩
  have := h2 _ (Finset.mem_singleton_self _)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 this
  linarith

/-- `x² + y²`: `t* = 1`. -/
theorem newtonDist_sq_add_sq : newtonDist ({![2, 0], ![0, 2]} : Finset (Fin 2 → ℝ)) = 1 := by
  refine newtonDist_eq (u := ![1 / 2, 1 / 2]) ⟨fun i => by fin_cases i <;> norm_num,
    by simp [Fin.sum_univ_two]; norm_num, ?_⟩ ?_
  · intro α hα
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> simp [Fin.sum_univ_two]
  · rintro t' u' ⟨-, h1, h2⟩
    have a := h2 ![2, 0] (by simp)
    have b := h2 ![0, 2] (by simp)
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 a b
    linarith

/-- `x²` in `d = 2` (non-compact face): `t* = 2`. -/
theorem newtonDist_sq_d2 : newtonDist ({![2, 0]} : Finset (Fin 2 → ℝ)) = 2 := by
  refine newtonDist_eq (u := ![1, 0]) ⟨fun i => by fin_cases i <;> norm_num,
    by simp [Fin.sum_univ_two], by simp [Fin.sum_univ_two]⟩ ?_
  rintro t' u' ⟨h0, h1, h2⟩
  have := h2 _ (Finset.mem_singleton_self _)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 this
  linarith [h0 1]

end SLT.Newton
