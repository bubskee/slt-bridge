/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
import VectorSLT
import SLT

/-!
# Zoo: Theorem M through the elementary template (brief 03, T1 guardrail)

This file re-derives `VectorSLT.ZN1_two_sided` (`Z_{N,1} ≍ N⁻⁴ (log N)⁴` at position one of the
depth-four shear network) by routing its upper half through the core's elementary template
(`SLT/Template/*`).

**What the template replaces.** In `vector-slt-lean`, the row bound is
`pivotRow = lemmaM4 + lemmaM5`. Here:
* Lemma M5 (amplitude integral and radial split) is **not used**. It is replaced by the core
  theorems `SLT.Template.minLogBound_pivotCone` (critical weight on a pivot cone) and
  `SLT.Template.lintegral_le_rate_of_minLogBound` (slice bound ⇒ one extra log);
* `two_rows` (the triangular Fubini F5) is replaced by `SLT.Template.lintegral_triangular`;
* the final assembly (`theoremM`, `theoremM_raw`) is replaced by the core's `LaplaceUpper`
  calculus (`comp_mul`, `const_mul`, `mono`).

**What is imported from `vector-slt-lean` and used as hypothesis dischargers.**
* Lemma M4 (`lemmaM4`, the slice bound at frozen amplitudes);
* Lemma M3 for the chart `E` (`m3Int_Echart`, uniform integrability of `|det|^{-1/2}`);
* (G↓) (`Gdown`) with the comparison `TMx_le_SMx`;
* the active-coordinate integrals F1–F3 (`UM_inner`);
* the lower bound, Proposition L′ (`Zpos_one_lower`);
* the coordinate plumbing (pivot permutations, the (M6) weights and their `WOK`/`WDOK` bounds).

The constants differ from the source's (`CrowT` against `CM5`), so the statement of the re-derived
theorem is the source's with the same quantifier structure. (`VectorSLT` is not written in the
`module` system, so this file is a plain, non-`module` file.)
-/

namespace SLT.Zoo.TemplateM

open MeasureTheory Set Filter VectorSLT SLT.Template
open VectorSLT.SLT (isqrt measurable_isqrt)
open scoped ENNReal

/-! ### The slice weight and its min-integral bound (replaces Lemma M5) -/

/-- The (M9) slice determinant of the pivot-first chart, as a function of the amplitudes. -/
noncomputable def chartD (yP yI yJ γ : T3 → ℝ) (a : T3) : ℝ :=
  a.2.1 / a.1 * (a.2.2 / a.1) *
    EM9 (a.2.1 / a.1) (a.2.2 / a.1) (yI a / yP a) (yJ a / yP a) (a.1 ^ 3 / γ a)

/-- The slice weight `|a_p|⁻³ |D|^{-1/2}` of Lemma M4. -/
noncomputable def rowWeight (yP yI yJ γ : T3 → ℝ) (a : T3) : ℝ≥0∞ :=
  ENNReal.ofReal (|a.1|⁻¹ ^ 3) * isqrt (chartD yP yI yJ γ a)

/-- Its angular part at radius `r`: `|q a' E_r(q, a')|^{-1/2}`. -/
noncomputable def angW (yP yI yJ γ : T3 → ℝ) (r : ℝ) (q : Fin 2 → ℝ) : ℝ≥0∞ :=
  isqrt (q 0) * isqrt (q 1) * isqrt (Echart yP yI yJ γ r (q 0, q 1))

/-- The source's pivot region is the core's pivot cone, through `e2`. -/
theorem pivotRegion_eq (ε : ℝ) : pivotRegion ε = e2 ⁻¹' pivotCone 2 ε := by
  ext a
  simp only [pivotRegion, pivotCone, mem_preimage, mem_ofPred_eq, e2_apply, Fin.forall_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- `e2⁻¹ (r, p) = (r, (p 0, p 1))`. -/
theorem e2_symm_apply (x : ℝ × (Fin 2 → ℝ)) : e2.symm x = (x.1, (x.2 0, x.2 1)) := rfl

/-- Lemma M3 for the chart `E`, transported to `[-1,1]²` as a subset of `Fin 2 → ℝ`. -/
theorem angW_int {ε : ℝ} (hε : 0 < ε) (hε20 : ε ≤ 1 / 20) {yP yI yJ γ : T3 → ℝ}
    (hmP : Measurable yP) (hmI : Measurable yI) (hmJ : Measurable yJ) (hmγ : Measurable γ)
    (hP : WOK ε yP) (hγ : WOK ε γ) (hIP : WDOK ε yI yP) (hJP : WDOK ε yJ yP)
    {r : ℝ} (hr : |r| ≤ ε) :
    ∫⁻ q in Icc (-1 : Fin 2 → ℝ) 1, angW yP yI yJ γ r q ≤ ENNReal.ofReal M3const := by
  have hM3 := m3Int_Echart hε hε20 hmP hmI hmJ hmγ hP hγ hIP hJP hr
  have hpre : Icc (-1 : Fin 2 → ℝ) 1 =
      MeasurableEquiv.finTwoArrow ⁻¹' (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) := by
    ext q
    simp only [mem_Icc, mem_preimage, mem_prod, MeasurableEquiv.finTwoArrow_apply,
      Pi.le_def, Fin.forall_fin_two, Pi.neg_apply, Pi.one_apply]
    tauto
  rw [hpre]
  have e := (volume_preserving_finTwoArrow ℝ).setLIntegral_comp_preimage_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding
    (fun p : ℝ × ℝ => isqrt p.1 * isqrt p.2 * isqrt (Echart yP yI yJ γ r p))
    (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
  exact (le_of_eq e).trans hM3

/-- The constant `B` of the row weight's min-integral bound. -/
noncomputable def Bcone (ε : ℝ) : ℝ :=
  2 * M3const * (1 + Real.posLog ε + Real.posLog (2 ^ 2 * (2 * ε) ^ 3 / M3const))

/-- **The row weight satisfies the logarithmic min-integral bound** on the pivot region:
Lemma M3 (uniform in the radius) through the core's `minLogBound_pivotCone`. -/
theorem rowWeight_minLogBound {ε : ℝ} (hε : 0 < ε) (hε20 : ε ≤ 1 / 20) {yP yI yJ γ : T3 → ℝ}
    (hmP : Measurable yP) (hmI : Measurable yI) (hmJ : Measurable yJ) (hmγ : Measurable γ)
    (hP : WOK ε yP) (hγ : WOK ε γ) (hIP : WDOK ε yI yP) (hJP : WDOK ε yJ yP) :
    MinLogBound (volume.restrict (pivotRegion ε)) (rowWeight yP yI yJ γ) ((2 * ε) ^ 3)
      (Bcone ε) (2 * M3const) := by
  have hwm : Measurable (rowWeight yP yI yJ γ) := by
    unfold rowWeight chartD EM9
    exact (by fun_prop : Measurable fun a : T3 => ENNReal.ofReal (|a.1|⁻¹ ^ 3)).mul
      (measurable_isqrt.comp (by fun_prop))
  have hcone := minLogBound_pivotCone (n := 2) hε (w := rowWeight yP yI yJ γ ∘ e2.symm)
    (hwm.comp e2.symm.measurable) (h := angW yP yI yJ γ) (H := M3const) (T := (2 * ε) ^ 3)
    M3const_pos (by positivity)
    (fun r _ hr => angW_int hε hε20 hmP hmI hmJ hmγ hP hγ hIP hJP hr)
    (fun r hr _ q _ => by
      simp only [Function.comp_apply, e2_symm_apply, rowWeight, chartD, angW, Echart,
        Pi.smul_apply, smul_eq_mul]
      rw [mul_div_cancel_left₀ _ hr, mul_div_cancel_left₀ _ hr, isqrt_mul, isqrt_mul])
  have h2 := hcone.comp_preimage mp_e2 e2.measurableEmbedding
  rw [← pivotRegion_eq] at h2
  have e : (rowWeight yP yI yJ γ ∘ e2.symm) ∘ e2 = rowWeight yP yI yJ γ := by
    funext a; simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  rw [e] at h2
  simpa [Bcone] using h2

/-! ### One row, pivot first, through the template -/

/-- The row constant produced by the template. -/
noncomputable def CrowT (ε : ℝ) : ℝ := fibreConst (2 * CM4 ε) (Bcone ε) (2 * M3const) 1

/-- **`pivotRow` through the elementary template**: the slice bound is Lemma M4, the weight bound
is Lemma M3 through `minLogBound_pivotCone`, and the log bookkeeping is
`lintegral_le_rate_of_minLogBound`. -/
theorem pivotRow_template {ε M : ℝ} (hε : 0 < ε) (hε20 : ε ≤ 1 / 20) (hM : Real.exp 1 ≤ M)
    {yP yI yJ γ : T3 → ℝ} (hmP : Measurable yP) (hmI : Measurable yI) (hmJ : Measurable yJ)
    (hmγ : Measurable γ) (hP : WOK ε yP) (hI : WOK ε yI) (hJ : WOK ε yJ) (hγ : WOK ε γ)
    (hIP : WDOK ε yI yP) (hJP : WDOK ε yJ yP) :
    ∫⁻ a in pivotRegion ε, ⨆ κ : ℝ, ∫⁻ b in Icc (-ε) ε ×ˢ square 0 ε,
        ENNReal.ofReal (rowInt yP yI yJ γ M κ a b) ≤
      ENNReal.ofReal (CrowT ε * M⁻¹ * Real.log M ^ 2) := by
  have hM1 : 1 ≤ M := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hM
  have hM0 : 0 < M := by linarith
  have hl1 : 1 ≤ Real.log M := SLT.one_le_log_of_exp_le hM
  have hε1 : ε ≤ 1 := by linarith
  have hCM4 : 0 < CM4 ε := by unfold CM4; have := Kslice_pos hε; positivity
  have hB : 0 ≤ Bcone ε := by
    unfold Bcone; have := M3const_pos
    have := Real.posLog_nonneg (x := ε)
    have := Real.posLog_nonneg (x := 2 ^ 2 * (2 * ε) ^ 3 / M3const)
    positivity
  have hrate2 : SLT.rate 1 2 M = M⁻¹ * Real.log M := by
    simp [SLT.rate, Real.rpow_neg_one]
  have hrate3 : SLT.rate 1 (2 + 1) M = M⁻¹ * Real.log M ^ 2 := by
    simp [SLT.rate, Real.rpow_neg_one]
  have key := lintegral_le_rate_of_minLogBound
    (rowWeight_minLogBound hε hε20 hmP hmI hmJ hmγ hP hγ hIP hJP) (mul_pos two_pos hCM4) hB
    (by have := M3const_pos; linarith) zero_le_one one_le_two hM
    (G := fun a => ⨆ κ : ℝ, ∫⁻ b in Icc (-ε) ε ×ˢ square 0 ε,
      ENNReal.ofReal (rowInt yP yI yJ γ M κ a b)) ?_
  · rw [hrate3] at key
    refine key.trans (le_of_eq ?_)
    rw [CrowT, mul_assoc]
  filter_upwards [ae_restrict_mem (measurableSet_pivotRegion ε),
    ae_restrict_of_ae ae_fst_ne_zero] with a ha ha0
  refine iSup_le fun κ => le_min ?_ ?_
  · exact lintegral_exp_neg_le_vol hε _ fun b => by positivity
  · obtain ⟨h1, h2, h3⟩ := ha
    have hb := pivotRegion_sub_box3 ⟨h1, h2, h3⟩
    refine (lemmaM4 hε hε1 hM1 ha0 h1 h2 h3 (hP.1 a hb) (hI.1 a hb) (hJ.1 a hb)
      (hγ.1 a hb)).trans ?_
    rw [rowWeight, ← mul_assoc,
      ← ENNReal.ofReal_mul (mul_nonneg (mul_pos two_pos hCM4).le (SLT.rate_nonneg 1 2 hM1))]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    rw [hrate2]
    have hx : 0 ≤ |a.1|⁻¹ ^ 3 := by positivity
    have hMi : 0 ≤ M⁻¹ := by positivity
    have : 1 + Real.log M ≤ 2 * Real.log M := by linarith
    calc CM4 ε * M⁻¹ * |a.1|⁻¹ ^ 3 * (1 + Real.log M)
        ≤ CM4 ε * M⁻¹ * |a.1|⁻¹ ^ 3 * (2 * Real.log M) := by gcongr
      _ = 2 * CM4 ε * (M⁻¹ * Real.log M) * |a.1|⁻¹ ^ 3 := by ring

/-! ### One row in its actual coordinates (the source's plumbing, with `pivotRow_template`) -/

/-- `rowBound` with the template's row constant. The proof is the source's covering of `[-ε,ε]³`
by three pivot regions, with `pivotRow` replaced by `pivotRow_template`. -/
theorem rowBound_template {ε M : ℝ} (hε : 0 < ε) (hε20 : ε ≤ 1 / 20) (hM : Real.exp 1 ≤ M)
    {y : ℕ → T3 → ℝ} {γ : T3 → ℝ} (hmy : ∀ i, Measurable (y i)) (hmγ : Measurable γ)
    (hy : ∀ i < 3, WOK ε (y i)) (hγ : WOK ε γ) (hyd : ∀ i < 3, ∀ l < 3, WDOK ε (y i) (y l)) :
    ∫⁻ a in box3 ε, ⨆ κ : ℝ, ∫⁻ b in box3 ε, ENNReal.ofReal (rowAct y γ M κ a b) ≤
      3 * ENNReal.ofReal (CrowT ε * M⁻¹ * Real.log M ^ 2) := by
  set Φ : T3 → ENNReal := fun a => ⨆ κ : ℝ, ∫⁻ b in box3 ε, ENNReal.ofReal (rowAct y γ M κ a b)
    with hΦ
  set B := ENNReal.ofReal (CrowT ε * M⁻¹ * Real.log M ^ 2)
  have hpart : ∀ p : Fin 3, ∫⁻ a in (pivMap p) ⁻¹' pivotRegion ε, Φ a ≤ B := by
    intro p
    have hπ := permOK_symm p
    obtain ⟨hP3, hI3, hJ3⟩ := pidx_lt p
    have hmeas : ∀ i, Measurable fun a => y i ((pivMap p).symm a) :=
      fun i => (hmy i).comp (pivMap p).symm.measurable
    have e1 : ∫⁻ a in (pivMap p) ⁻¹' pivotRegion ε, Φ a =
        ∫⁻ a' in pivotRegion ε, Φ ((pivMap p).symm a') := by
      have := (mp_pivMap p).setLIntegral_comp_preimage_emb (pivMap p).measurableEmbedding
        (fun a' => Φ ((pivMap p).symm a')) (pivotRegion ε)
      simpa only [MeasurableEquiv.symm_apply_apply] using this
    rw [e1]
    have hτ : MeasurePreserving (fun b => e2 (pivMap p b)) volume volume :=
      mp_e2.comp (mp_pivMap p)
    have hτe : MeasurableEmbedding fun b => e2 (pivMap p b) :=
      ((pivMap p).trans e2).measurableEmbedding
    have e3 : ∀ a' : T3, Φ ((pivMap p).symm a') = ⨆ κ : ℝ,
        ∫⁻ β in Icc (-ε) ε ×ˢ square 0 ε, ENNReal.ofReal (rowInt
          (fun a => y (pP p) ((pivMap p).symm a)) (fun a => y (pI p) ((pivMap p).symm a))
          (fun a => y (pJ p) ((pivMap p).symm a)) (fun a => γ ((pivMap p).symm a)) M κ a' β) := by
      intro a'
      simp only [hΦ]
      refine iSup_congr fun κ => ?_
      rw [box3_eq_preimage p ε]
      simp_rw [rowAct_piv p]
      exact hτ.setLIntegral_comp_preimage_emb hτe
        (fun β => ENNReal.ofReal (rowInt (fun a => y (pP p) ((pivMap p).symm a))
          (fun a => y (pI p) ((pivMap p).symm a)) (fun a => y (pJ p) ((pivMap p).symm a))
          (fun a => γ ((pivMap p).symm a)) M κ a' β)) _
    simp_rw [e3]
    exact pivotRow_template hε hε20 hM (hmeas _) (hmeas _) (hmeas _)
      (hmγ.comp (pivMap p).symm.measurable)
      ((hy _ hP3).comp hπ) ((hy _ hI3).comp hπ) ((hy _ hJ3).comp hπ) (hγ.comp hπ)
      ((hyd _ hI3 _ hP3).comp hπ) ((hyd _ hJ3 _ hP3).comp hπ)
  have hcover : box3 ε ⊆ (pivMap 0) ⁻¹' pivotRegion ε ∪
      ((pivMap 1) ⁻¹' pivotRegion ε ∪ (pivMap 2) ⁻¹' pivotRegion ε) := by
    rintro ⟨a0, a1, a2⟩ ⟨h0, h1, h2⟩
    simp only [mem_union, mem_preimage, pivMap, MeasurableEquiv.refl_apply, perm1_apply,
      perm2_apply, pivotRegion, mem_ofPred_eq]
    rcases le_total |a1| |a0| with c1 | c1 <;> rcases le_total |a2| |a0| with c2 | c2 <;>
      rcases le_total |a2| |a1| with c3 | c3
    all_goals first
      | exact Or.inl ⟨h0, c1, c2⟩
      | exact Or.inr (Or.inl ⟨h1, c1, c3⟩)
      | exact Or.inr (Or.inr ⟨h2, c2, c3⟩)
      | exact Or.inr (Or.inl ⟨h1, c1, by linarith⟩)
      | exact Or.inr (Or.inr ⟨h2, c2, by linarith⟩)
  calc ∫⁻ a in box3 ε, Φ a
      ≤ ∫⁻ a in (pivMap 0) ⁻¹' pivotRegion ε ∪
          ((pivMap 1) ⁻¹' pivotRegion ε ∪ (pivMap 2) ⁻¹' pivotRegion ε), Φ a :=
        lintegral_mono_set hcover
    _ ≤ (∫⁻ a in (pivMap 0) ⁻¹' pivotRegion ε, Φ a) +
          ((∫⁻ a in (pivMap 1) ⁻¹' pivotRegion ε, Φ a) +
            ∫⁻ a in (pivMap 2) ⁻¹' pivotRegion ε, Φ a) :=
        (lintegral_union_le _ _ _).trans (add_le_add le_rfl (lintegral_union_le _ _ _))
    _ ≤ B + (B + B) := add_le_add (hpart 0) (add_le_add (hpart 1) (hpart 2))
    _ = 3 * B := by ring

/-- `rowBound_M6` with the template's row constant. -/
theorem rowBound_M6_template {ε M : ℝ} (hε : 0 < ε) (hε20 : ε ≤ 1 / 20) (hM : Real.exp 1 ≤ M)
    {cy cg : ℝ} (hcy : |cy| ≤ 1 / 32) (hcg : |cg| ≤ 1 / 32) {g : T3 → T3} (hgm : Measurable g)
    (hg : GOK ε g) :
    ∫⁻ a in box3 ε, ⨆ κ : ℝ, ∫⁻ b in box3 ε,
        ENNReal.ofReal (rowAct (yRow cy g) (γRow cg) M κ a b) ≤
      3 * ENNReal.ofReal (CrowT ε * M⁻¹ * Real.log M ^ 2) :=
  rowBound_template hε hε20 hM (measurable_yRow cy hgm) (measurable_γRow cg)
    (fun i _ => yRow_WOK hε hε20 hcy hg i) (γRow_WOK hε hε20 hcg)
    (fun i _ l _ => yRow_WDOK hε hg i l)

/-! ### Two rows: the core's triangular Fubini (replaces `two_rows`) -/

/-- One row's bound from the template, `3 C N⁻¹ (log N)²`. -/
noncomputable def BrowT (M : ℝ) : ENNReal :=
  3 * ENNReal.ofReal (CrowT (1 / 20) * M⁻¹ * Real.log M ^ 2)

/-- The row bound is finite. -/
theorem BrowT_ne_top (M : ℝ) : BrowT M ≠ ⊤ :=
  ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top

/-- **`J(N; c) ≤ (3 C N⁻¹ (log N)²)²`** for both rows, via `SLT.Template.lintegral_triangular`. -/
theorem J_bound_template {M : ℝ} (hM : Real.exp 1 ≤ M) {c : ℝ × ℝ} (hc : c ∈ Ic ×ˢ Ic) :
    ∫⁻ w in Wbox, F0r M c w.1.1 w.1.2 w.2.1 * F1r M c w.2.1 w.2.2 w.1.1 ≤ BrowT M * BrowT M := by
  have hc1 : |c.1| ≤ 1 / 32 := abs_le.mpr hc.1
  have hc2 : |c.2| ≤ 1 / 32 := abs_le.mpr hc.2
  have hε : (0 : ℝ) < 1 / 20 := by norm_num
  set S := box3 (1 / 20)
  have hμ : (volume : Measure ((T3 × T3) × (T3 × T3))).restrict Wbox =
      ((volume.restrict S).prod (volume.restrict S)).prod
        ((volume.restrict S).prod (volume.restrict S)) := by
    rw [Wbox, Measure.volume_eq_prod (α := T3 × T3) (β := T3 × T3), ← Measure.prod_restrict,
      Measure.volume_eq_prod (α := T3) (β := T3), ← Measure.prod_restrict]
  rw [hμ]
  refine lintegral_triangular _ _ _ _ (F0r M c) (F1r M c) (measurable_F0r M c)
    (measurable_F1r M c) (BrowT_ne_top M) (fun a1 => ⨆ κ : ℝ, ∫⁻ b in box3 (1 / 20),
      ENNReal.ofReal (rowAct (yRow c.2 id) (γRow c.2) M κ a1 b)) ?_
    (fun a0 a1 => le_iSup (fun κ : ℝ => ∫⁻ b in box3 (1 / 20),
      ENNReal.ofReal (rowAct (yRow c.2 id) (γRow c.2) M κ a1 b)) _)
    (rowBound_M6_template hε le_rfl hM hc2 hc2 measurable_id (gok_id _))
  filter_upwards [ae_restrict_mem (measurableSet_box3 (1 / 20))] with a1 ha1
  refine le_trans (lintegral_mono fun a0 => ?_) (rowBound_M6_template hε le_rfl hM hc2 hc1
    (measurable_const (a := a1)) (gok_const ha1))
  exact le_iSup (fun κ : ℝ => ∫⁻ b in box3 (1 / 20),
    ENNReal.ofReal (rowAct (yRow c.2 fun _ => a1) (γRow c.1) M κ a0 b)) _

/-- F5 + F6 at fixed `c`, with the template's row bound. -/
theorem UM_c_template {M : ℝ} (hM : Real.exp 1 ≤ M) {c : ℝ × ℝ} (hc : c ∈ Ic ×ˢ Ic) :
    ∫⁻ w in Wbox, ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) *
        F0r M c w.1.1 w.1.2 w.2.1 * F1r M c w.2.1 w.2.2 w.1.1 ≤
      ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) * (BrowT M * BrowT M) := by
  have hm : Measurable fun w : (T3 × T3) × (T3 × T3) =>
      F0r M c w.1.1 w.1.2 w.2.1 * F1r M c w.2.1 w.2.2 w.1.1 :=
    ((measurable_F0r M c).comp (f := fun w : (T3 × T3) × (T3 × T3) => (w.1.1, w.1.2, w.2.1))
      (by fun_prop)).mul
    ((measurable_F1r M c).comp (f := fun w : (T3 × T3) × (T3 × T3) => (w.2.1, w.2.2, w.1.1))
      (by fun_prop))
  have e : ∫⁻ w in Wbox, ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) *
        F0r M c w.1.1 w.1.2 w.2.1 * F1r M c w.2.1 w.2.2 w.1.1 =
      ∫⁻ w in Wbox, ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) *
        (F0r M c w.1.1 w.1.2 w.2.1 * F1r M c w.2.1 w.2.2 w.1.1) :=
    lintegral_congr fun w => mul_assoc _ _ _
  rw [e, lintegral_const_mul _ hm]
  exact mul_le_mul' le_rfl (J_bound_template hM hc)

/-! ### The box integral and the upper rate -/

/-- The box integral of the (M5) form at inverse temperature `M`. -/
noncomputable def Fbox (M : ℝ) : ENNReal :=
  ∫⁻ y in UM, ENNReal.ofReal (Real.exp (-(M * TMx y.1.1.1 y.1.1.2 y.1.2.1 y.1.2.2 y.2.1.1
    y.2.1.2 y.2.2.1 y.2.2.2)))

/-- The box integral: `≤ (π/M)·¼·(π/M)·(3 C M⁻¹ (log M)²)²` (source's `UM_bound`, with the
template's rows). -/
theorem Fbox_le {M : ℝ} (hM : Real.exp 1 ≤ M) :
    Fbox M ≤ ENNReal.ofReal (Real.pi / M) * 4⁻¹ *
      (ENNReal.ofReal (Real.pi / M) * (BrowT M * BrowT M)) := by
  have hM0 : 0 < M := lt_of_lt_of_le (Real.exp_pos 1) hM
  have hfm : Measurable fun y : Raw16 => ENNReal.ofReal (Real.exp (-(M * TMx y.1.1.1 y.1.1.2
      y.1.2.1 y.1.2.2 y.2.1.1 y.2.1.2 y.2.2.1 y.2.2.2))) := by
    unfold TMx VectorSLT.Zr P1t P2t cub3; fun_prop
  have hU : UM = ((Iα ×ˢ Jν) ×ˢ (Iα ×ˢ Jν)) ×ˢ Wbox := rfl
  unfold Fbox
  rw [hU, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm _ hfm.aemeasurable]
  refine (setLIntegral_mono' measurableSet_Wbox fun w hw =>
    UM_inner hM0 w.1.1 w.1.2 w.2.1 w.2.2 hw.1.1 hw.2.1).trans ?_
  have hsw : Measurable (Function.uncurry fun (a : (T3 × T3) × (T3 × T3)) (c : ℝ × ℝ) =>
      ENNReal.ofReal (Real.exp (-(M * (c.1 ^ 2 + c.2 ^ 2)))) * F0r M c a.1.1 a.1.2 a.2.1 *
        F1r M c a.2.1 a.2.2 a.1.1) := by
    unfold Function.uncurry F0r F1r rowAct yRow γRow κr cub3
    simp only [pcub0, pcub1, pcub2, id]
    fun_prop
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)),
    lintegral_lintegral_swap hsw.aemeasurable]
  gcongr
  refine (setLIntegral_mono' (measurableSet_Icc.prod measurableSet_Icc) fun c hc =>
    UM_c_template hM hc).trans ?_
  rw [lintegral_mul_const _ (by fun_prop)]
  exact mul_le_mul' ((setLIntegral_le_lintegral _ _).trans (le_of_eq (lintegral_gauss2 hM0))) le_rfl

/-- The template's row constant is nonnegative. -/
theorem CrowT_nonneg : 0 ≤ CrowT (1 / 20) := by
  have h3 := M3const_pos
  have h4 : 0 < CM4 (1 / 20) := by
    unfold CM4; have := Kslice_pos (by norm_num : (0 : ℝ) < 1 / 20); positivity
  have hB : 0 ≤ Bcone (1 / 20) := by
    unfold Bcone
    have := Real.posLog_nonneg (x := (1 / 20 : ℝ))
    have := Real.posLog_nonneg (x := 2 ^ 2 * (2 * (1 / 20 : ℝ)) ^ 3 / M3const)
    positivity
  have := Real.posLog_nonneg (x := (2 * CM4 (1 / 20))⁻¹)
  unfold CrowT fibreConst
  positivity

/-- **The box integral has upper rate `(4, 5)`**: `Fbox M ≤ K M⁻⁴ (log M)⁴`. -/
theorem Fbox_laplaceUpper : SLT.LaplaceUpper Fbox 4 5 := by
  refine ⟨Real.pi ^ 2 * 9 * CrowT (1 / 20) ^ 2 / 4, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with M hM
  have hM0 : 0 < M := lt_of_lt_of_le (Real.exp_pos 1) hM
  have hl : 0 ≤ Real.log M :=
    Real.log_nonneg (le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hM)
  have hc := CrowT_nonneg
  refine (Fbox_le hM).trans (le_of_eq ?_)
  have hx : 0 ≤ CrowT (1 / 20) * M⁻¹ * Real.log M ^ 2 := by positivity
  have h3 : BrowT M = ENNReal.ofReal (3 * (CrowT (1 / 20) * M⁻¹ * Real.log M ^ 2)) := by
    rw [BrowT, ENNReal.ofReal_mul (p := 3) (by norm_num), ENNReal.ofReal_ofNat]
  have h4 : (4 : ENNReal)⁻¹ = ENNReal.ofReal (1 / 4) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  have hr : SLT.rate 4 5 M = M⁻¹ ^ 4 * Real.log M ^ 4 := by
    rw [SLT.rate, Real.rpow_neg hM0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, inv_pow]
  rw [h3, h4, hr, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

/-! ### Position one: the comparison, and the two-sided estimate -/

/-- **The comparison** (source's `theoremM`, pointwise part): `Z_{N,1} ≤ π₁ · Fbox (κ' N)` for some
`κ' > 0` and all `N ≥ 0`, from (G↓), (A1) and the raw cutoff. -/
theorem Zpos_le_Fbox (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ)
    (φ χ : Raw16 → ENNReal) {π₁ : ℝ} (hφ : ∀ θ, φ θ ≤ ENNReal.ofReal π₁)
    (hχ : ∀ θ, χ θ ≤ 1) (hχs : ∀ θ, 1 / 200 < ‖θ‖ → χ θ = 0) :
    ∃ κ' : ℝ, 0 < κ' ∧ ∀ N : ℝ, 0 ≤ N →
      Zpos μ A0 φ χ 0 N ≤ ENNReal.ofReal π₁ * Fbox (κ' * N) := by
  obtain ⟨κ, hκ, hG⟩ := Gdown μ hmom hlh hμ₀ hμ
  refine ⟨min κ 1 / 3, div_pos (lt_min hκ one_pos) (by norm_num), fun N hN0 => ?_⟩
  set κ' := min κ 1 / 3 with hκ'
  have hπ : ∀ θ, φ θ * χ (θ - basePos A0 0) ≤
      (toM2 ⁻¹' UM).indicator (fun _ => ENNReal.ofReal π₁) θ := by
    intro θ
    by_cases hθ : toM2 θ ∈ UM
    · rw [indicator_of_mem (show θ ∈ toM2 ⁻¹' UM from hθ)]
      calc φ θ * χ (θ - basePos A0 0) ≤ ENNReal.ofReal π₁ * 1 := mul_le_mul' (hφ θ) (hχ _)
        _ = _ := mul_one _
    · have : 1 / 200 < ‖θ - basePos A0 0‖ := by
        by_contra hc; exact hθ (toM2_mem_UM (not_lt.mp hc))
      rw [hχs _ this, mul_zero]; exact bot_le
  have hset : MeasurableSet (toM2 ⁻¹' UM) := measurableSet_UM.preimage measurable_toM2
  set g : Raw16 → ENNReal := fun y => ENNReal.ofReal (Real.exp (-((κ' * N) * TMx y.1.1.1 y.1.1.2
    y.1.2.1 y.1.2.2 y.2.1.1 y.2.1.2 y.2.2.1 y.2.2.2))) with hg
  have hgm : Measurable g := by simp only [hg]; unfold TMx VectorSLT.Zr P1t P2t cub3; fun_prop
  have hpt : ∀ θ ∈ toM2 ⁻¹' UM,
      ENNReal.ofReal (Real.exp (-(N * popLossA μ A0 θ))) ≤ g (toM2 θ) := by
    intro θ hθ
    obtain ⟨⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩, ⟨⟨ha0, hb0⟩, ⟨ha1, hb1⟩⟩⟩ := hθ
    have hT := TMx_le_SMx h0 h1 h2 h3 ha0 hb0 ha1 hb1
    have hS0 := SMx_nonneg (toM2 θ).1.1.1 (toM2 θ).1.1.2 (toM2 θ).1.2.1 (toM2 θ).1.2.2
      (toM2 θ).2.1.1 (toM2 θ).2.1.2 (toM2 θ).2.2.1 (toM2 θ).2.2.2
    have hGθ := hG θ
    rw [sum_coeffs_eq] at hGθ
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hmin : min κ 1 * SMx (toM2 θ).1.1.1 (toM2 θ).1.1.2 (toM2 θ).1.2.1 (toM2 θ).1.2.2
        (toM2 θ).2.1.1 (toM2 θ).2.1.2 (toM2 θ).2.2.1 (toM2 θ).2.2.2 ≤ popLossA μ A0 θ :=
      le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hS0) hGθ
    have hT0 : 0 ≤ TMx (toM2 θ).1.1.1 (toM2 θ).1.1.2 (toM2 θ).1.2.1 (toM2 θ).1.2.2
        (toM2 θ).2.1.1 (toM2 θ).2.1.2 (toM2 θ).2.2.1 (toM2 θ).2.2.2 := by unfold TMx; positivity
    have hm0 : 0 ≤ min κ 1 := le_min hκ.le zero_le_one
    rw [hκ']
    nlinarith [mul_le_mul_of_nonneg_left hT hm0, mul_le_mul_of_nonneg_left hmin hN0]
  calc Zpos μ A0 φ χ 0 N
      = ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * popLossA μ A0 θ))) *
          (φ θ * χ (θ - basePos A0 0)) := rfl
    _ ≤ ∫⁻ θ, ENNReal.ofReal (Real.exp (-(N * popLossA μ A0 θ))) *
          (toM2 ⁻¹' UM).indicator (fun _ => ENNReal.ofReal π₁) θ :=
        lintegral_mono fun θ => mul_le_mul' le_rfl (hπ θ)
    _ = ∫⁻ θ in toM2 ⁻¹' UM, ENNReal.ofReal (Real.exp (-(N * popLossA μ A0 θ))) *
          ENNReal.ofReal π₁ := by
        rw [← lintegral_indicator hset]
        refine lintegral_congr fun θ => ?_
        exact (indicator_mul_right (toM2 ⁻¹' UM)
          (fun θ => ENNReal.ofReal (Real.exp (-(N * popLossA μ A0 θ))))
          (fun _ => ENNReal.ofReal π₁)).symm
    _ ≤ ∫⁻ θ in toM2 ⁻¹' UM, g (toM2 θ) * ENNReal.ofReal π₁ :=
        setLIntegral_mono' hset fun θ hθ => mul_le_mul' (hpt θ hθ) le_rfl
    _ = (∫⁻ y in UM, g y) * ENNReal.ofReal π₁ := by
        have hgc : Measurable fun θ => g (toM2 θ) := hgm.comp measurable_toM2
        rw [lintegral_mul_const _ hgc,
          measurePreserving_toM2.setLIntegral_comp_preimage measurableSet_UM hgm]
    _ = ENNReal.ofReal π₁ * Fbox (κ' * N) := by rw [mul_comm]; rfl

/-- **Position one, upper rate `(4, 5)`, through the template.** -/
theorem Zpos_one_laplaceUpper (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ]
    (hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ)
    {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ)
    (φ χ : Raw16 → ENNReal) {π₁ : ℝ} (hφ : ∀ θ, φ θ ≤ ENNReal.ofReal π₁)
    (hχ : ∀ θ, χ θ ≤ 1) (hχs : ∀ θ, 1 / 200 < ‖θ‖ → χ θ = 0) :
    SLT.LaplaceUpper (Zpos μ A0 φ χ 0) 4 5 := by
  obtain ⟨κ', hκ', h⟩ := Zpos_le_Fbox μ hmom hlh hμ₀ hμ φ χ hφ hχ hχs
  refine ((Fbox_laplaceUpper.comp_mul hκ').const_mul (a := ENNReal.ofReal π₁)
    ENNReal.ofReal_ne_top).mono ?_
  filter_upwards [eventually_ge_atTop 0] with N hN
  exact h N hN

/-- **`Z_{N,1} ≍ N⁻⁴ (log N)⁴`, re-derived through the elementary template.** Same hypotheses
and conclusion as `VectorSLT.ZN1_two_sided`. The lower bound is Proposition L′
(`Zpos_one_lower`). The upper bound is `Zpos_one_laplaceUpper`, which uses the core's template
(`minLogBound_pivotCone`, `lintegral_le_rate_of_minLogBound`, `lintegral_triangular`) in place of
the source's Lemma M5, `two_rows` and `theoremM`. -/
theorem ZN1_two_sided_template (μ : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure μ] {R : ℝ}
    (hμR : ∀ᵐ x ∂μ, ∀ i, |x i| ≤ R) {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ}
    (hμ₀ : 0 < μ₀) (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ)
    (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ} (hφ₀ : 0 < φ₀) (hχ₀ : 0 < χ₀)
    (hφl : ∀ᶠ θ in nhds (basePos A0 0), ENNReal.ofReal φ₀ ≤ φ θ)
    (hχl : ∀ᶠ θ in nhds 0, ENNReal.ofReal χ₀ ≤ χ θ)
    (_hπ₁ : 0 ≤ π₁) (hφ : ∀ θ, φ θ ≤ ENNReal.ofReal π₁)
    (hχ : ∀ θ, χ θ ≤ 1) (hχs : ∀ θ, 1 / 200 < ‖θ‖ → χ θ = 0) :
    ∃ c C N₀ : ℝ, 0 < c ∧ ∀ N : ℝ, N₀ ≤ N →
      ENNReal.ofReal (c * N⁻¹ ^ 4 * Real.log N ^ 4) ≤ Zpos μ A0 φ χ 0 N ∧
        Zpos μ A0 φ χ 0 N ≤ ENNReal.ofReal (C * N⁻¹ ^ 4 * Real.log N ^ 4) := by
  have hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ := by
    intro i
    have hm : Measurable fun x : Fin 2 → ℝ => |x i| ^ (2 * 81) := by fun_prop
    refine Integrable.of_mem_Icc 0 (R ^ (2 * 81)) hm.aemeasurable ?_
    filter_upwards [hμR] with x hx
    exact ⟨by positivity, pow_le_pow_left₀ (abs_nonneg _) (hx i) _⟩
  obtain ⟨c, hc, N₁, hlow⟩ := Zpos_one_lower shearTarget_A0 μ hμR φ χ hφ₀ hχ₀ hφl hχl
  obtain ⟨C, N₂, hup⟩ := SLT.laplaceUpper_iff.mp
    (Zpos_one_laplaceUpper μ hmom hlh hμ₀ hμ φ χ hφ hχ hχs)
  refine ⟨c, C, max (max N₁ N₂) 1, hc, fun N hN => ⟨hlow N ?_, ?_⟩⟩
  · exact (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  · have hN0 : 0 < N := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hN)
    have e : N ^ (-(4 : ℝ)) = N⁻¹ ^ 4 := by
      rw [Real.rpow_neg hN0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        inv_pow]
    have := hup N ((le_max_right _ _).trans ((le_max_left _ _).trans hN))
    rwa [e] at this

/-- **Position one has learning pair `(4, 5)`**, in the core's predicate, with the upper half
through the template. -/
theorem position_one_pair_template (μ : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure μ] {R : ℝ}
    (hμR : ∀ᵐ x ∂μ, ∀ i, |x i| ≤ R) {lo hi : Fin 2 → ℝ} (hlh : ∀ i, lo i < hi i) {μ₀ : ℝ}
    (hμ₀ : 0 < μ₀) (hμ : ENNReal.ofReal μ₀ • volume.restrict (cbox lo hi) ≤ μ)
    (φ χ : Raw16 → ENNReal) {φ₀ χ₀ π₁ : ℝ} (hφ₀ : 0 < φ₀) (hχ₀ : 0 < χ₀)
    (hφl : ∀ᶠ θ in nhds (basePos A0 0), ENNReal.ofReal φ₀ ≤ φ θ)
    (hχl : ∀ᶠ θ in nhds 0, ENNReal.ofReal χ₀ ≤ χ θ)
    (_hπ₁ : 0 ≤ π₁) (hφ : ∀ θ, φ θ ≤ ENNReal.ofReal π₁)
    (hχ : ∀ θ, χ θ ≤ 1) (hχs : ∀ θ, 1 / 200 < ‖θ‖ → χ θ = 0) :
    SLT.HasLaplacePair (Zpos μ A0 φ χ 0) 4 5 := by
  have hmom : ∀ i, Integrable (fun x : Fin 2 → ℝ => |x i| ^ (2 * 81)) μ := by
    intro i
    have hm : Measurable fun x : Fin 2 → ℝ => |x i| ^ (2 * 81) := by fun_prop
    refine Integrable.of_mem_Icc 0 (R ^ (2 * 81)) hm.aemeasurable ?_
    filter_upwards [hμR] with x hx
    exact ⟨by positivity, pow_le_pow_left₀ (abs_nonneg _) (hx i) _⟩
  refine ⟨by norm_num, ?_, Zpos_one_laplaceUpper μ hmom hlh hμ₀ hμ φ χ hφ hχ hχs⟩
  obtain ⟨c, hc, N₁, hlow⟩ := Zpos_one_lower shearTarget_A0 μ hμR φ χ hφ₀ hχ₀ hφl hχl
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_ge_atTop (max N₁ 1)] with N hN
  have hN0 : 0 < N := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hN)
  have hr : SLT.rate 4 5 N = N⁻¹ ^ 4 * Real.log N ^ 4 := by
    rw [SLT.rate, Real.rpow_neg hN0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, inv_pow]
  rw [hr, ← mul_assoc]
  exact hlow N ((le_max_left _ _).trans hN)

end SLT.Zoo.TemplateM
