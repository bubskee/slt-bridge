/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.NormalCrossing.Step
public import SLT.Laplace.Pair

/-!
# Normal crossing on the cube `(0,1]^d`, with inactive coordinates

`ncZ k h N = ∫_{(0,1]^d} e^{-N ∏ xᵢ^{kᵢ}} ∏ xᵢ^{hᵢ} dx` for `kᵢ ∈ ℕ` and `hᵢ > -1`. Coordinates with
`kᵢ = 0` are *inactive*: they don't appear in the loss and contribute only the constant
`∫₀¹ x^{hᵢ} dx`. If some coordinate is active, the pair is

* `λ = min {(hᵢ+1)/kᵢ : kᵢ ≠ 0}` (`ncLam`),
* `m = #{i : kᵢ ≠ 0, (hᵢ+1)/kᵢ = λ}` (`ncMult`).

This generalises `vector-slt-lean`'s `normalCrossing` (exponents `2kᵢ`, all active). The
induction peels coordinate `0` with `NC.stepG`; an inactive coordinate is a constant factor
(`stepG_zero_exp`).
-/

@[expose] public section

namespace SLT.NC

open MeasureTheory Set Filter Real
open scoped ENNReal

/-- `Z(N) = ∫_{(0,1]^d} e^{-N ∏ xᵢ^{kᵢ}} ∏ xᵢ^{hᵢ} dx`. -/
noncomputable def ncZ {d : ℕ} (k : Fin d → ℕ) (h : Fin d → ℝ) (N : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Set.pi univ (fun _ => Ioc (0 : ℝ) 1),
    ENNReal.ofReal (Real.exp (-(N * ∏ i, x i ^ k i)) * ∏ i, x i ^ h i)

theorem ncZ_zero (k : Fin 0 → ℕ) (h : Fin 0 → ℝ) (N : ℝ) :
    ncZ k h N = ENNReal.ofReal (Real.exp (-N)) := by
  unfold ncZ
  rw [lintegral_unique, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  simp [volume_pi_pi]

theorem ncZ_succ {d : ℕ} (k : Fin (d + 1) → ℕ) (h : Fin (d + 1) → ℝ) (N : ℝ) :
    ncZ k h N = stepG (ncZ (Fin.tail k) (Fin.tail h)) (h 0) (k 0) N := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have he : ∀ x : Fin (d + 1) → ℝ, e x = (x 0, Fin.tail x) := fun x => rfl
  set T : Set (Fin d → ℝ) := Set.pi univ (fun _ => Ioc (0 : ℝ) 1)
  set f : ℝ × (Fin d → ℝ) → ℝ≥0∞ := fun p => ENNReal.ofReal
    (Real.exp (-(N * (p.1 ^ k 0 * ∏ j, p.2 j ^ k j.succ))) *
      (p.1 ^ h 0 * ∏ j, p.2 j ^ h j.succ))
  have hf : Measurable f := by fun_prop
  have hS : Set.pi univ (fun _ => Ioc (0 : ℝ) 1) = e ⁻¹' (Ioc 0 1 ×ˢ T) := by
    ext x
    simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_preimage, he, Set.mem_prod, T, Fin.tail]
    exact ⟨fun h => ⟨h 0, fun j => h j.succ⟩, fun h i => Fin.cases h.1 h.2 i⟩
  have hint : ∀ x : Fin (d + 1) → ℝ,
      ENNReal.ofReal (Real.exp (-(N * ∏ i, x i ^ k i)) * ∏ i, x i ^ h i) = f (e x) := by
    intro x; simp only [f, he, Fin.prod_univ_succ, Fin.tail]
  unfold ncZ
  simp_rw [hint]
  rw [hS, (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).setLIntegral_comp_preimage
    (measurableSet_Ioc.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)) hf,
    Measure.volume_eq_prod, setLIntegral_prod f hf.aemeasurable]
  unfold stepG
  refine setLIntegral_congr_fun measurableSet_Ioc fun x0 hx0 => ?_
  have hx : 0 ≤ x0 ^ h 0 := Real.rpow_nonneg hx0.1.le _
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) fun y _ => ?_
  simp only [f, Fin.tail]
  rw [← ENNReal.ofReal_mul hx]
  congr 1; ring_nf

/-! ### Constant factors and inactive coordinates -/

theorem stepG_const_mul (F : ℝ → ℝ≥0∞) {a : ℝ≥0∞} (ha : a ≠ ⊤) (h : ℝ) (k : ℕ) (N : ℝ) :
    stepG (fun M => a * F M) h k N = a * stepG F h k N := by
  unfold stepG
  simp_rw [mul_left_comm (ENNReal.ofReal _) a]
  rw [lintegral_const_mul' _ _ ha]

/-- An inactive coordinate (`k = 0`) is the constant factor `∫₀¹ x^h dx = 1/(h+1)`. -/
theorem stepG_zero_exp (F : ℝ → ℝ≥0∞) {h : ℝ} (hh : -1 < h) (N : ℝ) :
    stepG F h 0 N = ENNReal.ofReal (1 / (h + 1)) * F N := by
  unfold stepG
  simp only [pow_zero, mul_one]
  rw [lintegral_mul_const _ (by fun_prop), lintegral_Ioc_zero_rpow zero_le_one hh, Real.one_rpow]

theorem NCBound.const_mul {F : ℝ → ℝ≥0∞} {lam : ℝ} {m : ℕ} {c : ℝ} (hc : 0 < c)
    (hF : NCBound F lam m) : NCBound (fun M => ENNReal.ofReal c * F M) lam m := by
  obtain ⟨hmono, ⟨B, hB⟩, ⟨b, hb, hb1⟩, ⟨C, hC⟩, ⟨c', hc', M₀, hM₀⟩⟩ := hF
  refine ⟨fun M M' h1 h2 => by dsimp only; gcongr; exact hmono M M' h1 h2, ⟨c * B, ?_⟩,
    ⟨c * b, by positivity, ?_⟩, ⟨c * C, fun M hM => ?_⟩, ⟨c * c', by positivity, M₀, fun M hM => ?_⟩⟩
  · dsimp only; rw [ENNReal.ofReal_mul hc.le]; gcongr
  · dsimp only; rw [ENNReal.ofReal_mul hc.le]; gcongr
  · rw [show c * C * M ^ (-lam) * (1 + Real.log M) ^ (m - 1) =
      c * (C * M ^ (-lam) * (1 + Real.log M) ^ (m - 1)) by ring, ENNReal.ofReal_mul hc.le]
    dsimp only; gcongr; exact hC M hM
  · rw [show c * c' * M ^ (-lam) * Real.log M ^ (m - 1) =
      c * (c' * M ^ (-lam) * Real.log M ^ (m - 1)) by ring, ENNReal.ofReal_mul hc.le]
    dsimp only; gcongr; exact hM₀ M hM

/-! ### The exponents over the active coordinates -/

variable {d : ℕ}

/-- `μᵢ = (hᵢ + 1)/kᵢ`. -/
noncomputable def ncMu (k : Fin d → ℕ) (h : Fin d → ℝ) (i : Fin d) : ℝ := (h i + 1) / k i

/-- The active coordinates `{i : kᵢ ≠ 0}`. -/
def Active (k : Fin d → ℕ) : Finset (Fin d) := Finset.univ.filter fun i => k i ≠ 0

/-- `λ = min {μᵢ : kᵢ ≠ 0}` (and `0` if no coordinate is active). -/
noncomputable def ncLam (k : Fin d → ℕ) (h : Fin d → ℝ) : ℝ :=
  if hS : (Active k).Nonempty then (Active k).inf' hS (ncMu k h) else 0

/-- `m = #{i : kᵢ ≠ 0, μᵢ = λ}`. -/
noncomputable def ncMult (k : Fin d → ℕ) (h : Fin d → ℝ) : ℕ :=
  (Finset.univ.filter fun i => k i ≠ 0 ∧ ncMu k h i = ncLam k h).card

theorem mem_active {k : Fin d → ℕ} {i : Fin d} : i ∈ Active k ↔ k i ≠ 0 := by simp [Active]

theorem ncLam_le {k : Fin d → ℕ} {h : Fin d → ℝ} {i : Fin d} (hi : k i ≠ 0) :
    ncLam k h ≤ ncMu k h i := by
  have hS : (Active k).Nonempty := ⟨i, mem_active.mpr hi⟩
  rw [ncLam, dite_eq_left hS]; exact Finset.inf'_le _ (mem_active.mpr hi)

theorem exists_ncLam {k : Fin d → ℕ} {h : Fin d → ℝ} (hS : ∃ i, k i ≠ 0) :
    ∃ i, k i ≠ 0 ∧ ncMu k h i = ncLam k h := by
  have hS' : (Active k).Nonempty := let ⟨i, hi⟩ := hS; ⟨i, mem_active.mpr hi⟩
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' hS' (ncMu k h)
  exact ⟨i, mem_active.mp hi, by rw [ncLam, dite_eq_left hS', he]⟩

theorem ncLam_eq {k : Fin d → ℕ} {h : Fin d → ℝ} {L : ℝ} (hle : ∀ i, k i ≠ 0 → L ≤ ncMu k h i)
    (hex : ∃ i, k i ≠ 0 ∧ ncMu k h i = L) : ncLam k h = L := by
  obtain ⟨i, hi, hiL⟩ := hex
  obtain ⟨j, hj, hjL⟩ := exists_ncLam (h := h) ⟨i, hi⟩
  apply le_antisymm
  · rw [← hiL]; exact ncLam_le hi
  · rw [← hjL]; exact hle j hj

theorem ncLam_pos {k : Fin d → ℕ} {h : Fin d → ℝ} (hh : ∀ i, -1 < h i) (hS : ∃ i, k i ≠ 0) :
    0 < ncLam k h := by
  obtain ⟨i, hi, he⟩ := exists_ncLam (h := h) hS
  rw [← he, ncMu]
  have : (0 : ℝ) < k i := by exact_mod_cast Nat.pos_of_ne_zero hi
  have := hh i
  apply div_pos <;> linarith

theorem ncMult_pos {k : Fin d → ℕ} {h : Fin d → ℝ} (hS : ∃ i, k i ≠ 0) : 1 ≤ ncMult k h := by
  obtain ⟨i, hi, he⟩ := exists_ncLam (h := h) hS
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, he⟩⟩

theorem ncMult_succ (k : Fin (d + 1) → ℕ) (h : Fin (d + 1) → ℝ) :
    ncMult k h = (if k 0 ≠ 0 ∧ ncMu k h 0 = ncLam k h then 1 else 0) +
      (Finset.univ.filter fun j : Fin d => k j.succ ≠ 0 ∧ ncMu k h j.succ = ncLam k h).card := by
  unfold ncMult
  rw [Fin.card_filter_univ_succ]
  split_ifs <;> simp [add_comm]

/-! ### The induction -/

/-- **All the bounds.** With no active coordinate, `ncZ = c e^{-N}`; with one, `NCBound`. -/
theorem ncZ_cases : ∀ (d : ℕ) (k : Fin d → ℕ) (h : Fin d → ℝ), (∀ i, -1 < h i) →
    ((∀ i, k i = 0) → ∃ c : ℝ, 0 < c ∧
      ∀ N, ncZ k h N = ENNReal.ofReal c * ENNReal.ofReal (Real.exp (-N))) ∧
    ((∃ i, k i ≠ 0) → NCBound (ncZ k h) (ncLam k h) (ncMult k h))
  | 0, k, h, _ => ⟨fun _ => ⟨1, one_pos, fun N => by rw [ncZ_zero]; simp⟩,
      fun ⟨i, _⟩ => i.elim0⟩
  | d + 1, k, h, hh => by
    obtain ⟨IH0, IH1⟩ := ncZ_cases d (Fin.tail k) (Fin.tail h) (fun j => hh j.succ)
    have e : ncZ k h = stepG (ncZ (Fin.tail k) (Fin.tail h)) (h 0) (k 0) := funext (ncZ_succ k h)
    have hh0 : 0 < h 0 + 1 := by linarith [hh 0]
    by_cases htail : ∀ j, Fin.tail k j = 0
    · obtain ⟨c, hc, hZ⟩ := IH0 htail
      have eT : ncZ (Fin.tail k) (Fin.tail h) =
          fun M => ENNReal.ofReal c * ENNReal.ofReal (Real.exp (-M)) := funext hZ
      by_cases hk0 : k 0 = 0
      · -- every coordinate inactive
        refine ⟨fun _ => ⟨c * (1 / (h 0 + 1)), by positivity, fun N => ?_⟩, fun ⟨i, hi⟩ => ?_⟩
        · rw [e, eT, hk0, stepG_zero_exp _ (hh 0), ENNReal.ofReal_mul hc.le]; ring
        · exact (hi (Fin.cases (motive := fun i => k i = 0) hk0 (fun j => htail j) i)).elim
      · -- only coordinate `0` active: `(μ₀, 1)`
        refine ⟨fun hall => absurd (hall 0) hk0, fun _ => ?_⟩
        have hL : ncLam k h = ncMu k h 0 := by
          refine ncLam_eq (fun i hi => ?_) ⟨0, hk0, rfl⟩
          cases i using Fin.cases with
          | zero => exact le_rfl
          | succ j => exact absurd (htail j) hi
        have hM : ncMult k h = 1 := by
          rw [ncMult_succ, ite_eq_left ⟨hk0, hL.symm⟩]
          have : (Finset.univ.filter fun j : Fin d => k j.succ ≠ 0 ∧ ncMu k h j.succ = ncLam k h) = ∅ :=
            Finset.filter_false_of_mem fun j _ hj => hj.1 (htail j)
          rw [this]; rfl
        rw [e, eT, hL, hM]
        have hb := (NCBound.base (hh 0) (Nat.one_le_iff_ne_zero.mpr hk0)).const_mul hc
        have e2 : stepG (fun M => ENNReal.ofReal c * ENNReal.ofReal (Real.exp (-M))) (h 0) (k 0) =
            fun N => ENNReal.ofReal c *
              stepG (fun M => ENNReal.ofReal (Real.exp (-M))) (h 0) (k 0) N :=
          funext (stepG_const_mul _ ENNReal.ofReal_ne_top _ _)
        rw [e2]; exact hb
    · push Not at htail
      have htail' : ∃ j, Fin.tail k j ≠ 0 := htail
      have IH := IH1 htail'
      obtain ⟨j₀, hj₀⟩ := htail
      refine ⟨fun hall => absurd (hall j₀.succ) hj₀, fun _ => ?_⟩
      set lamt := ncLam (Fin.tail k) (Fin.tail h) with hlamt_def
      set mt := ncMult (Fin.tail k) (Fin.tail h) with hmt_def
      have hlamt : 0 < lamt := ncLam_pos (fun j => hh j.succ) htail'
      have hmt : 1 ≤ mt := ncMult_pos htail'
      obtain ⟨jm, hjm, hjme⟩ := exists_ncLam (h := Fin.tail h) htail'
      by_cases hk0 : k 0 = 0
      · -- inactive new coordinate: a constant factor
        have hL : ncLam k h = lamt := by
          refine ncLam_eq (fun i hi => ?_) ⟨jm.succ, hjm, hjme⟩
          cases i using Fin.cases with
          | zero => exact absurd hk0 hi
          | succ j => exact ncLam_le (k := Fin.tail k) hi
        have hM : ncMult k h = mt := by
          rw [ncMult_succ, ite_eq_right (fun hc => hc.1 hk0), zero_add, hL]; rfl
        rw [e, hL, hM, hk0]
        have eS : stepG (ncZ (Fin.tail k) (Fin.tail h)) (h 0) 0 =
            fun N => ENNReal.ofReal (1 / (h 0 + 1)) * ncZ (Fin.tail k) (Fin.tail h) N :=
          funext (stepG_zero_exp _ (hh 0))
        rw [eS]; exact IH.const_mul (by positivity)
      · have hk : 1 ≤ k 0 := Nat.one_le_iff_ne_zero.mpr hk0
        rcases lt_trichotomy (ncMu k h 0) lamt with hlt | heq | hgt
        · -- the new coordinate wins: `(μ₀, 1)`
          have hL : ncLam k h = ncMu k h 0 := by
            refine ncLam_eq (fun i hi => ?_) ⟨0, hk0, rfl⟩
            cases i using Fin.cases with
            | zero => exact le_rfl
            | succ j => exact hlt.le.trans (ncLam_le (k := Fin.tail k) hi)
          have hM : ncMult k h = 1 := by
            rw [ncMult_succ, ite_eq_left ⟨hk0, hL.symm⟩]
            have : (Finset.univ.filter fun j : Fin d => k j.succ ≠ 0 ∧ ncMu k h j.succ = ncLam k h) = ∅ := by
              refine Finset.filter_false_of_mem fun j _ hj => ?_
              have h1 : lamt ≤ ncMu (Fin.tail k) (Fin.tail h) j := ncLam_le hj.1
              have h2 : ncMu (Fin.tail k) (Fin.tail h) j = ncMu k h 0 := hj.2.trans hL
              linarith
            rw [this]; rfl
          rw [e, hL, hM]
          exact IH.step_gt (hh 0) hk hlt
        · -- a tie: one more logarithm
          have hL : ncLam k h = lamt := by
            refine ncLam_eq (fun i hi => ?_) ⟨jm.succ, hjm, hjme⟩
            cases i using Fin.cases with
            | zero => exact heq.ge
            | succ j => exact ncLam_le (k := Fin.tail k) hi
          have hM : ncMult k h = mt + 1 := by
            rw [ncMult_succ, ite_eq_left ⟨hk0, heq.trans hL.symm⟩, add_comm, hL]; rfl
          rw [e, hL, hM]
          exact IH.step_eq hmt (hh 0) hk heq.symm
        · -- the tail wins: `(lamt, mt)`
          have hL : ncLam k h = lamt := by
            refine ncLam_eq (fun i hi => ?_) ⟨jm.succ, hjm, hjme⟩
            cases i using Fin.cases with
            | zero => exact hgt.le
            | succ j => exact ncLam_le (k := Fin.tail k) hi
          have hM : ncMult k h = mt := by
            rw [ncMult_succ, ite_eq_right (fun hc => by rw [hL] at hc; exact hgt.ne' hc.2), zero_add, hL]
            rfl
          rw [e, hL, hM]
          exact IH.step_lt hlamt.le (hh 0) hk hgt

/-- From the induction bounds to a learning pair. -/
theorem NCBound.hasLaplacePair {F : ℝ → ℝ≥0∞} {lam : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hF : NCBound F lam m) : HasLaplacePair F lam m := by
  obtain ⟨-, -, -, ⟨C, hC⟩, ⟨c, hc, M₀, hlow⟩⟩ := hF
  refine ⟨hm, ⟨c, hc, ?_⟩, ⟨max C 0 * 2 ^ (m - 1), ?_⟩⟩
  · filter_upwards [eventually_ge_atTop M₀] with N hN
    rw [rate, ← mul_assoc]; exact hlow N hN
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
    have hN1 : 1 ≤ N := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hN
    have hN0 : 0 < N := by linarith
    have hl := one_le_log_of_exp_le hN
    refine (hC N hN1).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (1 + Real.log N) ^ (m - 1) ≤ 2 ^ (m - 1) * Real.log N ^ (m - 1) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) _
    have hp : 0 ≤ N ^ (-lam) := Real.rpow_nonneg hN0.le _
    unfold rate
    calc C * N ^ (-lam) * (1 + Real.log N) ^ (m - 1)
        ≤ max C 0 * N ^ (-lam) * (1 + Real.log N) ^ (m - 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
            (pow_nonneg (by linarith) _)
      _ ≤ max C 0 * N ^ (-lam) * (2 ^ (m - 1) * Real.log N ^ (m - 1)) := by
          apply mul_le_mul_of_nonneg_left h2; positivity
      _ = _ := by ring

/-- **The normal-crossing lemma on the cube.** For `hᵢ > -1` and at least one active coordinate,
`∫_{(0,1]^d} e^{-N ∏ xᵢ^{kᵢ}} ∏ xᵢ^{hᵢ} dx` has the pair `(ncLam k h, ncMult k h)`. -/
theorem ncZ_hasLaplacePair (k : Fin d → ℕ) (h : Fin d → ℝ) (hh : ∀ i, -1 < h i)
    (hS : ∃ i, k i ≠ 0) : HasLaplacePair (ncZ k h) (ncLam k h) (ncMult k h) :=
  ((ncZ_cases d k h hh).2 hS).hasLaplacePair (ncMult_pos hS)

end SLT.NC
