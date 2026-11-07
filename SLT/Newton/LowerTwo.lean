/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Newton.Upper

/-!
# The lower bound `H(L) ≳ e^{-L/t*} L^{dim O}` (N2)

Take `k + 1 = dim O + 1` affinely independent optimal weights `v_0, …, v_k ∈ O`
(`exists_optFamily`). They are linearly independent, since each has coordinate sum `1`. Choose
`k + 1` coordinates `I` that are injective on their span, and an index `i₀ ∈ I`. The linear map
`Λ θ = Σ_{i∈I} c_i(θ) v_{σ i} + Σ_{j∉I} θ_j e_j`, with `c_{i₀} = θ_{i₀} - Σ_{I∖i₀} θ` and
`c_i = θ_i` otherwise, is injective. It maps the box

  `θ_{i₀} ∈ [T, T+1]`, `θ_i ∈ [0, T/k]` for `i ∈ I∖i₀`, `θ_j ∈ [0,1]` for `j ∉ I`

into `S_L ∩ {⟨𝟙,x⟩ ≤ T + 1 + d}`, where `T = L/t*`. Since `φ ≥ t* Σ c_i` and `Σ c_i = θ_{i₀} ≥ T`,
this gives `H(L) ≥ e^{-(T+1+d)} |det Λ| (T/k)^k`.
-/

@[expose] public section

namespace SLT.Newton

open MeasureTheory Set Matrix Metric Filter Module
open scoped Pointwise

variable {d : ℕ}

/-- `k + 1` linearly independent optimal weights. -/
theorem exists_optFamily {Γ : Finset (Fin d → ℝ)} (hd : 0 < newtonDist Γ) :
    ∃ v : Fin (optDim Γ + 1) → Fin d → ℝ, (∀ q, v q ∈ optWeights Γ) ∧ LinearIndependent ℝ v := by
  obtain ⟨t, ht, hspan, hai⟩ := exists_affineIndependent ℝ (Fin d → ℝ) (optWeights Γ)
  have hli : LinearIndependent ℝ (fun x : t => (x : Fin d → ℝ)) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have hsum : ∑ j ∈ s, g j = 0 := by
      have := congrArg (fun v : Fin d → ℝ => ones ⬝ᵥ v) hg
      simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul, dotProduct_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ones_dotProduct, (ht j.2).2.1, mul_one]
    exact hai s g hsum (by rw [Finset.weightedVSub_eq_linear_combination _ hsum]; exact hg) i hi
  have hfin := hli.setFinite
  have : Fintype t := hfin.fintype
  have hne : t.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, AffineSubspace.span_empty, eq_comm, affineSpan_eq_bot] at hspan
    exact (optWeights_nonempty hd).ne_empty hspan
  have hcard : Fintype.card t = optDim Γ + 1 := by
    have : Nonempty t := hne.to_subtype
    have h := hai.finrank_vectorSpan_add_one
    rw [Subtype.range_coe, ← direction_affineSpan, hspan] at h
    exact h.symm
  set e := (Fintype.equivFin t).trans (finCongr hcard)
  refine ⟨fun q => (e.symm q : Fin d → ℝ), fun q => ht (e.symm q).2, ?_⟩
  exact hli.comp _ e.symm.injective

/-- **Lower bound**: `H(L) ≥ c e^{-L/t*} L^{dim O}` for `L > 0`. -/
theorem Hfun_ge {Γ : Finset (Fin d → ℝ)} (hΓ : ∀ α ∈ Γ, ∀ i, 0 ≤ α i) (hd : 0 < newtonDist Γ) :
    ∃ c : ℝ, 0 < c ∧ ∀ L : ℝ, 0 < L →
      ENNReal.ofReal (c * Real.exp (-(L * (newtonDist Γ)⁻¹)) * L ^ optDim Γ) ≤ Hfun Γ L := by
  classical
  obtain ⟨v, hvO, hvli⟩ := exists_optFamily hd
  generalize optDim Γ = k at *
  set τ := (newtonDist Γ)⁻¹
  have hτ : 0 < τ := inv_pos.mpr hd
  set W := Submodule.span ℝ (range v)
  have hW : finrank ℝ W = k + 1 := by rw [finrank_span_eq_card hvli, Fintype.card_fin]
  obtain ⟨I, hIle, hI⟩ := exists_coords_injOn W
  -- `|I| = k + 1`
  have hIcard : I.card = k + 1 := by
    refine le_antisymm (hW ▸ hIle) ?_
    set πI : W →ₗ[ℝ] ({i // i ∈ I} → ℝ) :=
      { toFun := fun w i => (w : Fin d → ℝ) i
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective πI := by
      intro a b hab
      have := hI (a - b) (a - b).2 fun i hi => by
        have := congrFun hab ⟨i, hi⟩
        simp only [πI, LinearMap.coe_mk, AddHom.coe_mk] at this
        simp [this]
      exact Subtype.ext (sub_eq_zero.mp this)
    have := LinearMap.finrank_le_finrank_of_injective hinj
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hW] at this
  have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i₀, hi₀⟩ := hIne
  set σ : {i // i ∈ I} ≃ Fin (k + 1) := I.equivFin.trans (finCongr hIcard)
  set bvec : Fin d → Fin d → ℝ := fun i =>
    if h : i ∈ I then v (σ ⟨i, h⟩) else Pi.single i 1
  set cf : (Fin d → ℝ) → Fin d → ℝ := fun θ i =>
    θ i - if i = i₀ then ∑ j ∈ I.erase i₀, θ j else 0
  have cf_add : ∀ x y i, cf (x + y) i = cf x i + cf y i := fun x y i => by
    simp only [cf, Pi.add_apply]; split_ifs <;> (try simp only [Finset.sum_add_distrib]) <;> ring
  have cf_smul : ∀ (a : ℝ) x i, cf (a • x) i = a * cf x i := fun a x i => by
    simp only [cf, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp only [Finset.mul_sum, mul_sub, sub_zero]
  set Λ : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
    { toFun := fun θ => ∑ i, cf θ i • bvec i
      map_add' := fun x y => by simp only [cf_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a x => by
        simp only [cf_smul, mul_smul, ← Finset.smul_sum, RingHom.id_apply] }
  have hΛ : ∀ θ, Λ θ = ∑ i, cf θ i • bvec i := fun _ => rfl
  -- the pieces of `Λ θ`
  have hbI : ∀ i (h : i ∈ I), bvec i = v (σ ⟨i, h⟩) := fun i h => by simp [bvec, h]
  have hbIc : ∀ i, i ∉ I → bvec i = Pi.single i 1 := fun i h => by simp [bvec, h]
  have hb0 : ∀ i m, 0 ≤ bvec i m := fun i m => by
    by_cases h : i ∈ I
    · rw [hbI i h]; exact (hvO _).1 m
    · rw [hbIc i h]; by_cases hm : m = i
      · subst hm; simp
      · simp [hm]
  have hb1 : ∀ i, ones ⬝ᵥ bvec i = 1 := fun i => by
    by_cases h : i ∈ I
    · rw [hbI i h, ones_dotProduct]; exact (hvO _).2.1
    · rw [hbIc i h, dotProduct_single, mul_one]; rfl
  -- injectivity
  have hinj : Function.Injective Λ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro θ hθ
    rw [hΛ] at hθ
    set w := ∑ i ∈ I, cf θ i • bvec i
    set y := ∑ i ∈ Finset.univ.filter (· ∉ I), cf θ i • bvec i
    have hwy : w + y = 0 := by
      rw [← hθ, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ I)]
      simp [w, y]
    have hyI : ∀ m ∈ I, y m = 0 := fun m hm => by
      simp only [y, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hiI : i ∉ I := (Finset.mem_filter.mp hi).2
      rw [hbIc i hiI]
      simp [show m ≠ i from fun h => hiI (h ▸ hm)]
    have hwW : w ∈ W := Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, (hbI i hi).symm⟩)
    have hw0 : w = 0 := hI w hwW fun m hm => by
      have := congrFun hwy m
      simp only [Pi.add_apply, Pi.zero_apply, hyI m hm, add_zero] at this
      exact this
    -- all `I`-coefficients vanish
    have hcI : ∀ i ∈ I, cf θ i = 0 := by
      have hsum : ∑ q, cf θ (σ.symm q) • v q = 0 := by
        rw [← hw0]
        simp only [w]
        rw [← Finset.sum_coe_sort I, ← σ.symm.sum_comp]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hbI _ (σ.symm q).2]
        simp
      have := Fintype.linearIndependent_iff.mp hvli _ hsum
      intro i hi
      have h := this (σ ⟨i, hi⟩)
      simpa using h
    have hy0 : y = 0 := by rw [hw0, zero_add] at hwy; exact hwy
    funext m
    by_cases hm : m ∈ I
    · by_cases hm0 : m = i₀
      · subst hm0
        have hrest : ∀ j ∈ I.erase m, θ j = 0 := fun j hj => by
          have := hcI j (Finset.mem_of_mem_erase hj)
          simpa [cf, Finset.ne_of_mem_erase hj] using this
        have := hcI m hm
        simp only [cf, Finset.sum_eq_zero hrest] at this
        simpa using this
      · have := hcI m hm
        simpa [cf, hm0] using this
    · have := congrFun hy0 m
      simp only [y, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [Finset.sum_eq_single m (fun i hi him => by
        rw [hbIc i (Finset.mem_filter.mp hi).2, Pi.single_apply, ite_eq_right (Ne.symm him), mul_zero])
        (fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ m, hm⟩) h),
        hbIc m hm, Pi.single_eq_same, mul_one] at this
      have hne : m ≠ i₀ := fun h => hm (h ▸ hi₀)
      simpa [cf, hne] using this
  have hdet : LinearMap.det Λ ≠ 0 := by
    have hu : IsUnit Λ := (LinearMap.isUnit_iff_ker_eq_bot Λ).mpr (LinearMap.ker_eq_bot.mpr hinj)
    exact ((LinearMap.isUnit_iff_isUnit_det Λ).mp hu).ne_zero
  -- the constant
  set c₀ : ℝ := (τ / k) ^ k
  have hc₀ : 0 < c₀ := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [c₀, hk]
    · exact pow_pos (div_pos hτ (by exact_mod_cast hk)) _
  refine ⟨Real.exp (-(1 + d)) * |LinearMap.det Λ| * c₀, by positivity, fun L hL => ?_⟩
  set T := L * τ
  have hT : 0 ≤ T := by positivity
  have hkT : (k : ℝ) * (T / k) ≤ T := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk, hT]
    · rw [mul_div_cancel₀ _ (by exact_mod_cast hk.ne')]
  set lo : Fin d → ℝ := fun i => if i = i₀ then T else 0
  set hi : Fin d → ℝ := fun i => if i = i₀ then T + 1 else if i ∈ I then T / k else 1
  have hwidth : ∀ i, hi i - lo i = if i ∈ I.erase i₀ then T / k else 1 := fun i => by
    simp only [hi, lo, Finset.mem_erase]
    by_cases h0 : i = i₀
    · simp [h0]
    · by_cases hI' : i ∈ I <;> simp [h0, hI']
  have hvol : volume (Icc lo hi) = ENNReal.ofReal ((T / k) ^ k) := by
    rw [Real.volume_Icc_pi]
    simp only [hwidth]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by split_ifs <;> positivity),
      Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, Finset.card_erase_of_mem hi₀,
      hIcard, Nat.add_sub_cancel]
  -- `Λ` maps the box into the cone, with `⟨𝟙,x⟩ ≤ T + 1 + d`
  have hmaps : ∀ θ ∈ Icc lo hi, Λ θ ∈ logCone Γ L ∧ ones ⬝ᵥ Λ θ ≤ T + 1 + d := by
    rintro θ ⟨hlo, hhi⟩
    have hθlo : ∀ i, lo i ≤ θ i := hlo
    have hθhi : ∀ i, θ i ≤ hi i := hhi
    have hrest : ∀ j ∈ I.erase i₀, 0 ≤ θ j ∧ θ j ≤ T / k := fun j hj => by
      have h1 := hθlo j; have h2 := hθhi j
      simp only [lo, hi, Finset.ne_of_mem_erase hj, ite_false, Finset.mem_of_mem_erase hj,
        ite_true] at h1 h2
      exact ⟨h1, h2⟩
    have hsumrest : ∑ j ∈ I.erase i₀, θ j ≤ T := by
      calc ∑ j ∈ I.erase i₀, θ j ≤ ∑ _j ∈ I.erase i₀, T / k :=
            Finset.sum_le_sum fun j hj => (hrest j hj).2
        _ = k * (T / k) := by
            rw [Finset.sum_const, Finset.card_erase_of_mem hi₀, hIcard, nsmul_eq_mul]; simp
        _ ≤ T := hkT
    have hθ0 : T ≤ θ i₀ ∧ θ i₀ ≤ T + 1 := by
      have h1 := hθlo i₀; have h2 := hθhi i₀
      simp only [lo, hi, ite_true] at h1 h2
      exact ⟨h1, h2⟩
    have hcf0 : ∀ i, 0 ≤ cf θ i := fun i => by
      simp only [cf]
      by_cases h0 : i = i₀
      · rw [ite_eq_left h0, h0]; linarith [hθ0.1]
      · rw [ite_eq_right h0, sub_zero]
        have := hθlo i
        simp only [lo, ite_eq_right h0] at this
        exact this
    have hsumI : ∑ i ∈ I, cf θ i = θ i₀ := by
      simp only [cf, Finset.sum_sub_distrib, Finset.sum_ite_eq', ite_eq_left hi₀]
      rw [← Finset.add_sum_erase I θ hi₀]; ring
    have hcfIc : ∀ i, i ∉ I → cf θ i = θ i := fun i h => by
      have : i ≠ i₀ := fun e => h (e ▸ hi₀)
      simp [cf, this]
    have hsplit : ∀ f : Fin d → ℝ, ∑ i, f i = ∑ i ∈ I, f i + ∑ i ∈ Finset.univ.filter (· ∉ I), f i :=
      fun f => by rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ I)]; simp
    refine ⟨⟨fun m => ?_, fun α hα => ?_⟩, ?_⟩
    · rw [hΛ, Finset.sum_apply]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hcf0 i) (hb0 i m)
    · rw [hΛ, dotProduct_sum]
      simp only [dotProduct_smul, smul_eq_mul]
      rw [hsplit]
      have hI' : ∑ i ∈ I, cf θ i * (α ⬝ᵥ bvec i) ≥ ∑ i ∈ I, cf θ i * newtonDist Γ :=
        Finset.sum_le_sum fun i hi => by
          rw [hbI i hi]
          refine mul_le_mul_of_nonneg_left ?_ (hcf0 i)
          have := (hvO (σ ⟨i, hi⟩)).2.2 α hα
          simpa [dotProduct] using this
      have hIc : 0 ≤ ∑ i ∈ Finset.univ.filter (· ∉ I), cf θ i * (α ⬝ᵥ bvec i) :=
        Finset.sum_nonneg fun i hi => by
          rw [hbIc i (Finset.mem_filter.mp hi).2, dotProduct_single, mul_one]
          exact mul_nonneg (hcf0 i) (hΓ α hα i)
      rw [← Finset.sum_mul, hsumI] at hI'
      have : L ≤ θ i₀ * newtonDist Γ := by
        calc L = T * newtonDist Γ := by simp only [T, τ]; field_simp
          _ ≤ θ i₀ * newtonDist Γ := mul_le_mul_of_nonneg_right hθ0.1 hd.le
      linarith
    · rw [hΛ, dotProduct_sum]
      simp only [dotProduct_smul, smul_eq_mul, hb1, mul_one]
      rw [hsplit, hsumI]
      have : ∑ i ∈ Finset.univ.filter (· ∉ I), cf θ i ≤ d := by
        calc ∑ i ∈ Finset.univ.filter (· ∉ I), cf θ i
            ≤ ∑ _i ∈ Finset.univ.filter (· ∉ I), (1 : ℝ) := Finset.sum_le_sum fun i hiF => by
              have hiI := (Finset.mem_filter.mp hiF).2
              rw [hcfIc i hiI]
              have := hθhi i
              have hne : i ≠ i₀ := fun e => hiI (e ▸ hi₀)
              simpa [hi, hne, hiI] using this
          _ ≤ ∑ _i : Fin d, (1 : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => zero_le_one
          _ = d := by simp
      linarith [hθ0.2]
  -- assemble
  have hsub : Λ '' Icc lo hi ⊆ logCone Γ L := by
    rintro _ ⟨θ, hθ, rfl⟩; exact (hmaps θ hθ).1
  calc ENNReal.ofReal (Real.exp (-(1 + d)) * |LinearMap.det Λ| * c₀ * Real.exp (-(L * τ)) * L ^ k)
      = ENNReal.ofReal (Real.exp (-(T + 1 + d))) *
          (ENNReal.ofReal |LinearMap.det Λ| * ENNReal.ofReal ((T / k) ^ k)) := by
        rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        have he : Real.exp (-(T + 1 + d)) = Real.exp (-(1 + d)) * Real.exp (-T) := by
          rw [← Real.exp_add]; ring_nf
        rw [he, show (T / k) ^ k = c₀ * L ^ k by simp only [c₀, T]; rw [← mul_pow]; ring_nf]
        ring
    _ = ENNReal.ofReal (Real.exp (-(T + 1 + d))) * volume (Λ '' Icc lo hi) := by
        rw [Measure.addHaar_image_linearMap, hvol]
    _ = ∫⁻ _x in Λ '' Icc lo hi, ENNReal.ofReal (Real.exp (-(T + 1 + d))) :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in Λ '' Icc lo hi, ENNReal.ofReal (Real.exp (-(ones ⬝ᵥ x))) := by
        refine setLIntegral_mono (by
          show Measurable fun x : Fin d → ℝ => ENNReal.ofReal (Real.exp (-(∑ i, ones i * x i)))
          fun_prop) fun x hx => ?_
        obtain ⟨θ, hθ, rfl⟩ := hx
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [(hmaps θ hθ).2]))
    _ ≤ Hfun Γ L := lintegral_mono_set hsub

end SLT.Newton
