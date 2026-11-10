/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Basic
public import SLT.MiddlePositions.Two.Kernel

/-!
# The suffix kernel on unit discs

The rest of Lemma "Weighted two-form suffix" of `complex_middle_positions.tex`: the free
coefficient `q₀ = z` is integrated over all of `ℂ`, and the result is integrated over a unit disc
in `Q = q₁`.

* `lintegral_coords`: Lebesgue measure on cubic space in the coordinates `(z, Q, u, v)`.
* `disc_coords`: `𝔇(z, Q, u, v) = v² ((z - c)² - δ)` with `h = u² - Q v`,
  `c = u (u² - 3h) / v²` and `δ = 4h³/v⁴` (the note's completed square).
* `lintegral_F_coords_le`: for `|u|, |v| < 1`, `∫_ℂ F(z, Q, u, v) dz ≤ C · G(Q, u, v)`. The
  degenerate fibres `v = 0` and `h = 0` need no separate null-set argument: there `G = ∞`.
* `setLIntegral_box_F_le`: `∫_{|P₁ - Q₀| < 1, |P₂| < 1, |P₃| < 1} F ≤ C`, uniformly in `Q₀`.
-/

@[expose] public section

namespace SLT.MiddlePositions.Two

open MeasureTheory Set Real Metric SLT.PositionFour SLT.PositionFour.Downstream SLT.Pushforward
open scoped ENNReal NNReal

/-! ### Coordinates `(z, Q, u, v)` -/

/-- The cubic with moment coordinates `(z, Q, u, v)`, read from `(Q, (v, (u, z)))`. -/
def ofCoords (p : ℂ × (ℂ × (ℂ × ℂ))) : Cubic := ![p.2.2.2, p.1, p.2.2.1, p.2.1]

/-- The measurable equivalence `(Q, (v, (u, z))) ↦ (z, Q, u, v)`. -/
noncomputable def coordsEquiv : ℂ × (ℂ × (ℂ × ℂ)) ≃ᵐ Cubic where
  toFun := ofCoords
  invFun P := (P 1, (P 3, (P 2, P 0)))
  left_inv _ := rfl
  right_inv P := by funext i; fin_cases i <;> rfl
  measurable_toFun := by
    refine measurable_pi_iff.mpr fun i => ?_
    fin_cases i
    exacts [measurable_snd.snd.snd, measurable_fst, measurable_snd.snd.fst, measurable_snd.fst]
  measurable_invFun := by
    change Measurable fun P : Cubic => (P 1, (P 3, (P 2, P 0)))
    fun_prop

/-- `coordsEquiv` preserves Lebesgue measure. -/
theorem measurePreserving_coordsEquiv : MeasurePreserving coordsEquiv volume volume := by
  refine ⟨coordsEquiv.measurable, ?_⟩
  rw [MeasureTheory.volume_pi]
  refine (Measure.pi_eq fun s _ => ?_).symm
  rw [MeasurableEquiv.map_apply]
  have hpre : coordsEquiv ⁻¹' univ.pi s = s 1 ×ˢ (s 3 ×ˢ (s 2 ×ˢ s 0)) := by
    ext ⟨Q, v, u, z⟩
    simp only [mem_preimage, mem_univ_pi, mem_prod, Fin.forall_fin_succ, IsEmpty.forall_iff,
      and_true]
    simp only [coordsEquiv, MeasurableEquiv.coe_mk, Fin.isValue, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two]
    tauto
  rw [hpre, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    Measure.volume_eq_prod, Measure.prod_prod, Fin.prod_univ_four]
  ring

/-- **Tonelli in the coordinates `(z, Q, u, v)`**, with `z` innermost:
`∫ f(P) dP = ∫ dQ ∫ dv ∫ du ∫ dz f(z, Q, u, v)`. -/
theorem lintegral_coords {f : Cubic → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ P, f P = ∫⁻ Q, ∫⁻ v, ∫⁻ u, ∫⁻ z, f ![z, Q, u, v] := by
  rw [← measurePreserving_coordsEquiv.lintegral_comp_emb coordsEquiv.measurableEmbedding]
  have hm : Measurable fun p => f (coordsEquiv p) := hf.comp coordsEquiv.measurable
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  refine lintegral_congr fun Q => ?_
  have hm1 : Measurable fun p : ℂ × (ℂ × ℂ) => f (coordsEquiv (Q, p)) :=
    hm.comp measurable_prodMk_left
  rw [Measure.volume_eq_prod, lintegral_prod _ hm1.aemeasurable]
  refine lintegral_congr fun v => ?_
  have hm2 : Measurable fun p : ℂ × ℂ => f (coordsEquiv (Q, (v, p))) :=
    hm1.comp measurable_prodMk_left
  rw [Measure.volume_eq_prod, lintegral_prod _ hm2.aemeasurable]
  rfl

/-! ### The density in coordinates -/

/-- **The completed square** (the note's proof of Lemma "Weighted two-form suffix"): with
`h = u² - Q v`, `𝔇(z, Q, u, v) = v² ((z - u(u² - 3h)/v²)² - 4h³/v⁴)` for `v ≠ 0`. -/
theorem disc_coords {z Q u v : ℂ} (hv : v ≠ 0) :
    disc ![z, Q, u, v] = v ^ 2 * ((z - u * (u ^ 2 - 3 * (u ^ 2 - Q * v)) / v ^ 2) ^ 2 -
      4 * (u ^ 2 - Q * v) ^ 3 / v ^ 4) := by
  simp only [disc, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- `‖(z, Q, u, v)‖ ≤ |z| + (1 + |Q|)` for `|u|, |v| < 1`. -/
theorem norm_coords_le {z Q u v : ℂ} (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) :
    ‖(![z, Q, u, v] : Cubic)‖ ≤ ‖z‖ + (1 + ‖Q‖) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  fin_cases i <;> simp <;> linarith [norm_nonneg z, norm_nonneg Q]

/-- `F(P) ≤ |𝔇|^{-4/3} + (a^{1/4} + b^{1/4}) |𝔇|^{-11/8}` when `‖P‖ ≤ a + b`. -/
theorem F_le {P : Cubic} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hP : ‖P‖ ≤ a + b) :
    F P ≤ ‖disc P‖ₑ⁻¹ ^ (4 / 3 : ℝ) +
      (ENNReal.ofReal (a ^ (1 / 4 : ℝ)) + ENNReal.ofReal (b ^ (1 / 4 : ℝ))) *
        ‖disc P‖ₑ⁻¹ ^ (11 / 8 : ℝ) := by
  unfold F twoCubeDensity
  rw [← enorm_eq_nnnorm]
  gcongr
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal ((Real.rpow_le_rpow (norm_nonneg _) hP (by norm_num)).trans
    (Real.rpow_add_le_add_rpow ha hb (by norm_num) (by norm_num)))

/-! ### The `z`-integration -/

/-- The constant of `lintegral_F_coords_le`. -/
noncomputable def Mz (K₁ K₂ : ℝ) : ℝ := K₁ + K₂ + 4 * quadW K₂ (11 / 8) (1 / 4) + 1

/-- The real inequality behind the weighted term: with `x = |v|`, `y = |h|`, `|c| ≤ (1 + 3y)/x²`
and `δ = 4y³/x⁴`, `W (x²)^{-11/8} δ^{-3/8} (|c|^{1/4} + δ^{1/8}) ≤
4W x^{-7/4} (y^{-9/8} + y^{-7/8} + y^{-3/4})`. -/
theorem weighted_term_le {x y cn W : ℝ} (hx : 0 < x) (hy : 0 < y) (hc0 : 0 ≤ cn)
    (hc : cn ≤ (1 + 3 * y) / x ^ 2) (hW : 0 ≤ W) :
    W * (x ^ 2) ^ (-(11 / 8 : ℝ)) * (4 * y ^ 3 / x ^ 4) ^ (1 - 11 / 8 : ℝ) *
        (cn ^ (1 / 4 : ℝ) + (4 * y ^ 3 / x ^ 4) ^ ((1 / 4 : ℝ) / 2)) ≤
      4 * W * (x ^ (-(7 / 4 : ℝ)) *
        (y ^ (-(9 / 8 : ℝ)) + y ^ (-(7 / 8 : ℝ)) + y ^ (-(3 / 4 : ℝ)))) := by
  have iden := sq_rpow_mul_rpow_eq hx hy (11 / 8)
  have hf : (4 : ℝ) ^ (1 - 11 / 8 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have e1 : x ^ (2 * (11 / 8 : ℝ) - 4) = x ^ (-(5 / 4 : ℝ)) := by norm_num
  have e2 : y ^ (3 - 3 * (11 / 8 : ℝ)) = y ^ (-(9 / 8 : ℝ)) := by norm_num
  have hxh : x ^ (-(1 / 2 : ℝ)) = (x ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hx.le _
  have c1 : cn ^ (1 / 4 : ℝ) ≤ (1 + 3 * y ^ (1 / 4 : ℝ)) * x ^ (-(1 / 2 : ℝ)) := by
    have h3 : (3 : ℝ) ^ (1 / 4 : ℝ) ≤ 3 :=
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)).trans_eq (Real.rpow_one 3)
    calc cn ^ (1 / 4 : ℝ) ≤ ((1 + 3 * y) / x ^ 2) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hc0 hc (by norm_num)
      _ = (1 + 3 * y) ^ (1 / 4 : ℝ) * x ^ (-(1 / 2 : ℝ)) := by
          rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul hx.le, hxh, div_eq_mul_inv]
          norm_num
      _ ≤ (1 + 3 * y ^ (1 / 4 : ℝ)) * x ^ (-(1 / 2 : ℝ)) := by
          gcongr
          calc (1 + 3 * y) ^ (1 / 4 : ℝ) ≤ 1 ^ (1 / 4 : ℝ) + (3 * y) ^ (1 / 4 : ℝ) :=
                Real.rpow_add_le_add_rpow (by norm_num) (by positivity) (by norm_num)
                  (by norm_num)
            _ = 1 + 3 ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ) := by
                rw [Real.one_rpow, Real.mul_rpow (by norm_num) hy.le]
            _ ≤ 1 + 3 * y ^ (1 / 4 : ℝ) := by gcongr
  have c2 : (4 * y ^ 3 / x ^ 4) ^ ((1 / 4 : ℝ) / 2) ≤ 4 * y ^ (3 / 8 : ℝ) * x ^ (-(1 / 2 : ℝ)) := by
    have h4 : (4 : ℝ) ^ (1 / 8 : ℝ) ≤ 4 :=
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)).trans_eq (Real.rpow_one 4)
    rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul hy.le, ← Real.rpow_natCast, ← Real.rpow_mul hx.le,
      hxh, div_eq_mul_inv]
    norm_num
    gcongr
  have p1 : x ^ (-(5 / 4 : ℝ)) * x ^ (-(1 / 2 : ℝ)) = x ^ (-(7 / 4 : ℝ)) :=
    rpow_mul_rpow_eq hx (by norm_num)
  have p2 : y ^ (-(9 / 8 : ℝ)) * y ^ (1 / 4 : ℝ) = y ^ (-(7 / 8 : ℝ)) :=
    rpow_mul_rpow_eq hy (by norm_num)
  have p3 : y ^ (-(9 / 8 : ℝ)) * y ^ (3 / 8 : ℝ) = y ^ (-(3 / 4 : ℝ)) :=
    rpow_mul_rpow_eq hy (by norm_num)
  have hX : 0 ≤ x ^ (-(5 / 4 : ℝ)) := by positivity
  have hY : 0 ≤ y ^ (-(9 / 8 : ℝ)) := by positivity
  have h7 : 0 ≤ x ^ (-(7 / 4 : ℝ)) := by positivity
  have hY7 : 0 ≤ y ^ (-(7 / 8 : ℝ)) := by positivity
  have hY6 : 0 ≤ y ^ (-(3 / 4 : ℝ)) := by positivity
  calc W * (x ^ 2) ^ (-(11 / 8 : ℝ)) * (4 * y ^ 3 / x ^ 4) ^ (1 - 11 / 8 : ℝ) *
        (cn ^ (1 / 4 : ℝ) + (4 * y ^ 3 / x ^ 4) ^ ((1 / 4 : ℝ) / 2))
      = W * (4 ^ (1 - 11 / 8 : ℝ) * x ^ (-(5 / 4 : ℝ)) * y ^ (-(9 / 8 : ℝ))) *
          (cn ^ (1 / 4 : ℝ) + (4 * y ^ 3 / x ^ 4) ^ ((1 / 4 : ℝ) / 2)) := by
        rw [mul_assoc W, iden, e1, e2]
    _ ≤ W * (1 * x ^ (-(5 / 4 : ℝ)) * y ^ (-(9 / 8 : ℝ))) *
          ((1 + 3 * y ^ (1 / 4 : ℝ)) * x ^ (-(1 / 2 : ℝ)) +
            4 * y ^ (3 / 8 : ℝ) * x ^ (-(1 / 2 : ℝ))) := by gcongr
    _ = W * (x ^ (-(5 / 4 : ℝ)) * x ^ (-(1 / 2 : ℝ))) *
          (y ^ (-(9 / 8 : ℝ)) + 3 * (y ^ (-(9 / 8 : ℝ)) * y ^ (1 / 4 : ℝ)) +
            4 * (y ^ (-(9 / 8 : ℝ)) * y ^ (3 / 8 : ℝ))) := by ring
    _ = W * x ^ (-(7 / 4 : ℝ)) * (y ^ (-(9 / 8 : ℝ)) + 3 * y ^ (-(7 / 8 : ℝ)) +
          4 * y ^ (-(3 / 4 : ℝ))) := by rw [p1, p2, p3]
    _ ≤ _ := by
        have : y ^ (-(9 / 8 : ℝ)) + 3 * y ^ (-(7 / 8 : ℝ)) + 4 * y ^ (-(3 / 4 : ℝ)) ≤
            4 * (y ^ (-(9 / 8 : ℝ)) + y ^ (-(7 / 8 : ℝ)) + y ^ (-(3 / 4 : ℝ))) := by linarith
        calc W * x ^ (-(7 / 4 : ℝ)) * (y ^ (-(9 / 8 : ℝ)) + 3 * y ^ (-(7 / 8 : ℝ)) +
              4 * y ^ (-(3 / 4 : ℝ)))
            ≤ W * x ^ (-(7 / 4 : ℝ)) *
                (4 * (y ^ (-(9 / 8 : ℝ)) + y ^ (-(7 / 8 : ℝ)) + y ^ (-(3 / 4 : ℝ)))) := by
              gcongr
          _ = _ := by ring

/-- The real inequality behind the two unweighted terms:
`K 4^{1-t} (x²)^{-t} (4y³/x⁴)^{1-t} ≤ K x^{2t-4} y^{3-3t}` for `t ≥ 1`. -/
theorem unweighted_term_le {x y K t : ℝ} (hx : 0 < x) (hy : 0 < y) (hK : 0 ≤ K) (ht : 1 ≤ t) :
    K * 4 ^ (1 - t) * (x ^ 2) ^ (-t) * (4 * y ^ 3 / x ^ 4) ^ (1 - t) ≤
      K * (x ^ (2 * t - 4) * y ^ (3 - 3 * t)) := by
  have iden := sq_rpow_mul_rpow_eq hx hy t
  have hf : (4 : ℝ) ^ (1 - t) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hf0 : 0 ≤ (4 : ℝ) ^ (1 - t) := by positivity
  have hXY : 0 ≤ x ^ (2 * t - 4) * y ^ (3 - 3 * t) := by positivity
  calc K * 4 ^ (1 - t) * (x ^ 2) ^ (-t) * (4 * y ^ 3 / x ^ 4) ^ (1 - t)
      = K * (4 ^ (1 - t) * 4 ^ (1 - t)) * (x ^ (2 * t - 4) * y ^ (3 - 3 * t)) := by
        rw [mul_assoc (K * 4 ^ (1 - t)), iden]; ring
    _ ≤ K * 1 * (x ^ (2 * t - 4) * y ^ (3 - 3 * t)) := by
        gcongr
        nlinarith
    _ = _ := by ring

/-- **The free coefficient integrated over all of `ℂ`** (the note's proof of Lemma
"Weighted two-form suffix", first part): for `|u|, |v| < 1`,
`∫_ℂ F(z, Q, u, v) dz ≤ Mz · G(Q, u, v)`. -/
theorem lintegral_F_coords_le {K₁ K₂ : ℝ} (hK₁ : FullPlaneQuadratic (4 / 3) K₁)
    (hK₂ : FullPlaneQuadratic (11 / 8) K₂) (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂) {Q u v : ℂ}
    (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) :
    ∫⁻ z, F ![z, Q, u, v] ≤ ENNReal.ofReal (Mz K₁ K₂) * G Q u v := by
  have hW0 : 0 ≤ quadW K₂ (11 / 8) (1 / 4) := quadW_nonneg hK₂0 (by norm_num) (by norm_num)
  have hMz : 0 < Mz K₁ K₂ := by unfold Mz; positivity
  have htop : ∀ {x : ℝ≥0∞}, x = ⊤ → ∫⁻ z, F ![z, Q, u, v] ≤ ENNReal.ofReal (Mz K₁ K₂) * x := by
    intro x hx
    rw [hx, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hMz).ne']
    exact le_top
  -- the degenerate fibres: `G = ∞`
  rcases eq_or_ne v 0 with rfl | hv0
  · apply htop
    simp only [G]
    rw [enorm_zero_inv_rpow (by norm_num), ENNReal.top_mul (enorm_inv_rpow_ne_zero _ (by norm_num))]
    simp
  rcases eq_or_ne (u ^ 2 - Q * v) 0 with hh0 | hh0
  · apply htop
    simp only [G]
    rw [hh0, enorm_zero_inv_rpow (by norm_num),
      ENNReal.mul_top (enorm_inv_rpow_ne_zero _ (by norm_num))]
    simp
  -- the generic fibre
  set A := v ^ 2 with hA_def
  set c := u * (u ^ 2 - 3 * (u ^ 2 - Q * v)) / v ^ 2 with hc_def
  set δ := 4 * (u ^ 2 - Q * v) ^ 3 / v ^ 4 with hδ_def
  have hA : A ≠ 0 := pow_ne_zero 2 hv0
  have hδ : δ ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hh0)) (pow_ne_zero 4 hv0)
  set R := (1 + ‖Q‖) ^ (1 / 4 : ℝ) with hR
  have hpt : ∀ z : ℂ, F ![z, Q, u, v] ≤ ‖A * ((z - c) ^ 2 - δ)‖ₑ⁻¹ ^ (4 / 3 : ℝ) +
      (ENNReal.ofReal (‖z‖ ^ (1 / 4 : ℝ)) + ENNReal.ofReal R) *
        ‖A * ((z - c) ^ 2 - δ)‖ₑ⁻¹ ^ (11 / 8 : ℝ) := fun z => by
    rw [← disc_coords hv0]
    exact F_le (norm_nonneg _) (by positivity) (norm_coords_le hu hv)
  set x := ‖v‖ with hx_def
  set y := ‖u ^ 2 - Q * v‖ with hy_def
  have hx : 0 < x := norm_pos_iff.mpr hv0
  have hy : 0 < y := norm_pos_iff.mpr hh0
  have hnA : ‖A‖ = x ^ 2 := norm_pow _ _
  have hnδ : ‖δ‖ = 4 * y ^ 3 / x ^ 4 := by
    rw [hδ_def, norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_ofNat]
  have hnc : ‖c‖ ≤ (1 + 3 * y) / x ^ 2 := by
    rw [hc_def, norm_div, norm_mul, norm_pow]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have h1 : ‖u ^ 2 - 3 * (u ^ 2 - Q * v)‖ ≤ ‖u‖ ^ 2 + 3 * y := by
      calc ‖u ^ 2 - 3 * (u ^ 2 - Q * v)‖ ≤ ‖u ^ 2‖ + ‖3 * (u ^ 2 - Q * v)‖ := norm_sub_le _ _
        _ = _ := by rw [norm_pow, norm_mul, Complex.norm_ofNat]
    have hu0 := norm_nonneg u
    calc ‖u‖ * ‖u ^ 2 - 3 * (u ^ 2 - Q * v)‖ ≤ ‖u‖ * (‖u‖ ^ 2 + 3 * y) := by gcongr
      _ ≤ 1 + 3 * y := by nlinarith
  have hU1 := lintegral_inv_quadratic_le (c := c) hK₁ hK₁0 hA hδ
  have hU2 := lintegral_inv_quadratic_le (c := c) hK₂ hK₂0 hA hδ
  have hWt := lintegral_rpow_mul_inv_quadratic_le (c := c) hK₂ hK₂0 (by norm_num)
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num) (by norm_num) hA hδ
  rw [hnA, hnδ] at hU1 hU2 hWt
  -- the three real bounds
  have b1 := unweighted_term_le hx hy hK₁0 (by norm_num : (1 : ℝ) ≤ 4 / 3)
  have b2 := unweighted_term_le hx hy hK₂0 (by norm_num : (1 : ℝ) ≤ 11 / 8)
  have b3 := weighted_term_le hx hy (norm_nonneg c) hnc hW0
  rw [show x ^ (2 * (4 / 3 : ℝ) - 4) = x ^ (-(4 / 3 : ℝ)) by norm_num,
    show y ^ (3 - 3 * (4 / 3 : ℝ)) = y ^ (-1 : ℝ) by norm_num] at b1
  rw [show x ^ (2 * (11 / 8 : ℝ) - 4) = x ^ (-(5 / 4 : ℝ)) by norm_num,
    show y ^ (3 - 3 * (11 / 8 : ℝ)) = y ^ (-(9 / 8) : ℝ) by norm_num] at b2
  -- the three terms of `G`, in real form
  have g1 : ‖v‖ₑ⁻¹ ^ (4 / 3 : ℝ) * ‖u ^ 2 - Q * v‖ₑ⁻¹ ^ (1 : ℝ) =
      ENNReal.ofReal (x ^ (-(4 / 3 : ℝ)) * y ^ (-1 : ℝ)) := by
    rw [enorm_inv_rpow_of_ne_zero hv0, enorm_inv_rpow_of_ne_zero hh0,
      ← ENNReal.ofReal_mul (by positivity)]
  have g2 : ‖v‖ₑ⁻¹ ^ (5 / 4 : ℝ) * ‖u ^ 2 - Q * v‖ₑ⁻¹ ^ (9 / 8 : ℝ) =
      ENNReal.ofReal (x ^ (-(5 / 4 : ℝ)) * y ^ (-(9 / 8) : ℝ)) := by
    rw [enorm_inv_rpow_of_ne_zero hv0, enorm_inv_rpow_of_ne_zero hh0,
      ← ENNReal.ofReal_mul (by positivity)]
  have g3 : ‖v‖ₑ⁻¹ ^ (7 / 4 : ℝ) * (‖u ^ 2 - Q * v‖ₑ⁻¹ ^ (9 / 8 : ℝ) +
      ‖u ^ 2 - Q * v‖ₑ⁻¹ ^ (7 / 8 : ℝ) + ‖u ^ 2 - Q * v‖ₑ⁻¹ ^ (3 / 4 : ℝ)) =
      ENNReal.ofReal (x ^ (-(7 / 4 : ℝ)) *
        (y ^ (-(9 / 8 : ℝ)) + y ^ (-(7 / 8 : ℝ)) + y ^ (-(3 / 4 : ℝ)))) := by
    rw [enorm_inv_rpow_of_ne_zero hv0, enorm_inv_rpow_of_ne_zero hh0,
      enorm_inv_rpow_of_ne_zero hh0, enorm_inv_rpow_of_ne_zero hh0,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  have hG : G Q u v = ENNReal.ofReal (x ^ (-(4 / 3 : ℝ)) * y ^ (-1 : ℝ)) +
      ENNReal.ofReal R * ENNReal.ofReal (x ^ (-(5 / 4 : ℝ)) * y ^ (-(9 / 8) : ℝ)) +
      ENNReal.ofReal (x ^ (-(7 / 4 : ℝ)) *
        (y ^ (-(9 / 8 : ℝ)) + y ^ (-(7 / 8 : ℝ)) + y ^ (-(3 / 4 : ℝ)))) := by
    rw [← g1, ← g2, ← g3]; rfl
  have hm43 : Measurable fun z : ℂ => ‖A * ((z - c) ^ 2 - δ)‖ₑ⁻¹ ^ (4 / 3 : ℝ) := by fun_prop
  have hm118 : Measurable fun z : ℂ => ‖A * ((z - c) ^ 2 - δ)‖ₑ⁻¹ ^ (11 / 8 : ℝ) := by fun_prop
  calc ∫⁻ z, F ![z, Q, u, v]
      ≤ ∫⁻ z, (‖A * ((z - c) ^ 2 - δ)‖ₑ⁻¹ ^ (4 / 3 : ℝ) +
          (ENNReal.ofReal (‖z‖ ^ (1 / 4 : ℝ)) + ENNReal.ofReal R) *
            ‖A * ((z - c) ^ 2 - δ)‖ₑ⁻¹ ^ (11 / 8 : ℝ)) := lintegral_mono hpt
    _ = (∫⁻ z, ‖A * ((z - c) ^ 2 - δ)‖ₑ⁻¹ ^ (4 / 3 : ℝ)) +
          (∫⁻ z, ENNReal.ofReal (‖z‖ ^ (1 / 4 : ℝ)) * ‖A * ((z - c) ^ 2 - δ)‖ₑ⁻¹ ^ (11 / 8 : ℝ)) +
          ENNReal.ofReal R * ∫⁻ z, ‖A * ((z - c) ^ 2 - δ)‖ₑ⁻¹ ^ (11 / 8 : ℝ) := by
        simp_rw [add_mul]
        rw [lintegral_add_left hm43, lintegral_add_left (by fun_prop),
          lintegral_const_mul _ hm118, add_assoc]
    _ ≤ ENNReal.ofReal (K₁ * 4 ^ (1 - 4 / 3 : ℝ) * (x ^ 2) ^ (-(4 / 3 : ℝ)) *
            (4 * y ^ 3 / x ^ 4) ^ (1 - 4 / 3 : ℝ)) +
          ENNReal.ofReal (quadW K₂ (11 / 8) (1 / 4) * (x ^ 2) ^ (-(11 / 8 : ℝ)) *
            (4 * y ^ 3 / x ^ 4) ^ (1 - 11 / 8 : ℝ) *
            (‖c‖ ^ (1 / 4 : ℝ) + (4 * y ^ 3 / x ^ 4) ^ ((1 / 4 : ℝ) / 2))) +
          ENNReal.ofReal R * ENNReal.ofReal (K₂ * 4 ^ (1 - 11 / 8 : ℝ) *
            (x ^ 2) ^ (-(11 / 8 : ℝ)) * (4 * y ^ 3 / x ^ 4) ^ (1 - 11 / 8 : ℝ)) := by
        gcongr
    _ ≤ ENNReal.ofReal (Mz K₁ K₂ * (x ^ (-(4 / 3 : ℝ)) * y ^ (-1 : ℝ))) +
          ENNReal.ofReal (Mz K₁ K₂ * (x ^ (-(7 / 4 : ℝ)) *
            (y ^ (-(9 / 8 : ℝ)) + y ^ (-(7 / 8 : ℝ)) + y ^ (-(3 / 4 : ℝ))))) +
          ENNReal.ofReal R * ENNReal.ofReal (Mz K₁ K₂ *
            (x ^ (-(5 / 4 : ℝ)) * y ^ (-(9 / 8) : ℝ))) := by
        have hk1 : K₁ ≤ Mz K₁ K₂ := by unfold Mz; linarith
        have hk2 : K₂ ≤ Mz K₁ K₂ := by unfold Mz; linarith
        have hk3 : 4 * quadW K₂ (11 / 8) (1 / 4) ≤ Mz K₁ K₂ := by unfold Mz; linarith
        refine add_le_add (add_le_add (ENNReal.ofReal_le_ofReal (b1.trans ?_))
          (ENNReal.ofReal_le_ofReal (b3.trans ?_)))
          (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (b2.trans ?_)) bot_le)
        · exact mul_le_mul_of_nonneg_right hk1 (by positivity)
        · exact mul_le_mul_of_nonneg_right hk3 (by positivity)
        · exact mul_le_mul_of_nonneg_right hk2 (by positivity)
    _ = ENNReal.ofReal (Mz K₁ K₂) * G Q u v := by
        rw [hG, ENNReal.ofReal_mul hMz.le, ENNReal.ofReal_mul hMz.le, ENNReal.ofReal_mul hMz.le]
        ring

/-! ### The suffix kernel on a unit disc -/

/-- The suffix box `{P : |P₁ - Q₀| < 1, |P₂| < 1, |P₃| < 1}`. -/
def box (Q₀ : ℂ) : Set Cubic := {P | ‖P 1 - Q₀‖ < 1 ∧ ‖P 2‖ < 1 ∧ ‖P 3‖ < 1}

/-- The suffix box is measurable. -/
theorem measurableSet_box (Q₀ : ℂ) : MeasurableSet (box Q₀) := by
  have h1 : MeasurableSet {P : Cubic | ‖P 1 - Q₀‖ < 1} :=
    measurableSet_lt (by fun_prop) measurable_const
  have h2 : MeasurableSet {P : Cubic | ‖P 2‖ < 1} := measurableSet_lt (by fun_prop) measurable_const
  have h3 : MeasurableSet {P : Cubic | ‖P 3‖ < 1} := measurableSet_lt (by fun_prop) measurable_const
  exact h1.inter (h2.inter h3)

/-- The constant of `setLIntegral_box_F_le`. -/
noncomputable def Msuf (K₀ K₁ K₂ : ℝ) : ℝ := Mz K₁ K₂ * (16 * π * Lc K₀) * (18 * π)

/-- **The suffix kernel on a unit `Q`-disc is uniformly bounded**: for every `Q₀ ∈ ℂ`,
`∫_{|P₁ - Q₀| < 1, |P₂| < 1, |P₃| < 1} F(P) dP ≤ Msuf`. The free coefficient `P₀` is integrated
over all of `ℂ`. -/
theorem setLIntegral_box_F_le {K₀ K₁ K₂ : ℝ} (hK₀ : FullPlaneQuadratic (9 / 8) K₀)
    (hK₁ : FullPlaneQuadratic (4 / 3) K₁) (hK₂ : FullPlaneQuadratic (11 / 8) K₂)
    (hK₀0 : 0 ≤ K₀) (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂) (Q₀ : ℂ) :
    ∫⁻ P in box Q₀, F P ≤ ENNReal.ofReal (Msuf K₀ K₁ K₂) := by
  set iQ := (ball Q₀ 1).indicator (1 : ℂ → ℝ≥0∞)
  set i1 := (ball (0 : ℂ) 1).indicator (1 : ℂ → ℝ≥0∞)
  set M := ENNReal.ofReal (Mz K₁ K₂)
  have hM : M ≠ ⊤ := ENNReal.ofReal_ne_top
  have hz : ∀ Q v u, ∫⁻ z, (box Q₀).indicator F ![z, Q, u, v] ≤
      iQ Q * (i1 v * (i1 u * (M * G Q u v))) := by
    intro Q v u
    by_cases h : Q ∈ ball Q₀ 1 ∧ v ∈ ball (0 : ℂ) 1 ∧ u ∈ ball (0 : ℂ) 1
    · obtain ⟨hQ, hv, hu⟩ := h
      have hmem : ∀ z : ℂ, ![z, Q, u, v] ∈ box Q₀ := fun z => by
        refine ⟨?_, ?_, ?_⟩
        · simpa [dist_eq_norm] using hQ
        · simpa using hu
        · simpa using hv
      simp only [indicator_of_mem (hmem _), iQ, i1, indicator_of_mem hQ, indicator_of_mem hv,
        indicator_of_mem hu, Pi.one_apply, one_mul]
      exact lintegral_F_coords_le hK₁ hK₂ hK₁0 hK₂0 (mem_ball_zero_iff.mp hu)
        (mem_ball_zero_iff.mp hv)
    · have hnot : ∀ z : ℂ, ![z, Q, u, v] ∉ box Q₀ := fun z hz' => by
        obtain ⟨h1, h2, h3⟩ := hz'
        refine h ⟨?_, ?_, ?_⟩
        · simpa [dist_eq_norm] using h1
        · simpa using h3
        · simpa using h2
      simp only [indicator_of_notMem (hnot _), lintegral_zero]
      exact bot_le
  have hu : ∀ Q v, ∫⁻ u, iQ Q * (i1 v * (i1 u * (M * G Q u v))) =
      iQ Q * (i1 v * (M * ∫⁻ u in ball (0 : ℂ) 1, G Q u v)) := by
    intro Q v
    rw [lintegral_const_mul' _ _ (indicator_one_ne_top _ _),
      lintegral_const_mul' _ _ (indicator_one_ne_top _ _)]
    congr 2
    rw [← lintegral_const_mul' _ _ hM, ← lintegral_indicator measurableSet_ball]
    exact lintegral_congr fun u => by by_cases hu : u ∈ ball (0 : ℂ) 1 <;> simp [i1, hu]
  have hv : ∀ Q, ∫⁻ v, iQ Q * (i1 v * (M * ∫⁻ u in ball (0 : ℂ) 1, G Q u v)) =
      iQ Q * (M * ∫⁻ v in ball (0 : ℂ) 1, ∫⁻ u in ball (0 : ℂ) 1, G Q u v) := by
    intro Q
    rw [lintegral_const_mul' _ _ (indicator_one_ne_top _ _)]
    congr 1
    rw [← lintegral_const_mul' _ _ hM, ← lintegral_indicator measurableSet_ball]
    exact lintegral_congr fun v => by by_cases hv : v ∈ ball (0 : ℂ) 1 <;> simp [i1, hv]
  rw [← lintegral_indicator (measurableSet_box Q₀),
    lintegral_coords (measurable_F.indicator (measurableSet_box Q₀))]
  calc ∫⁻ Q, ∫⁻ v, ∫⁻ u, ∫⁻ z, (box Q₀).indicator F ![z, Q, u, v]
      ≤ ∫⁻ Q, ∫⁻ v, ∫⁻ u, iQ Q * (i1 v * (i1 u * (M * G Q u v))) :=
        lintegral_mono fun Q => lintegral_mono fun v => lintegral_mono fun u => hz Q v u
    _ = ∫⁻ Q, iQ Q * (M * ∫⁻ v in ball (0 : ℂ) 1, ∫⁻ u in ball (0 : ℂ) 1, G Q u v) := by
        refine lintegral_congr fun Q => ?_
        simp_rw [hu]
        exact hv Q
    _ ≤ ∫⁻ Q, iQ Q * (M * (ENNReal.ofReal (16 * π * Lc K₀) * N2b Q)) := by
        gcongr with Q
        exact lintegral_G_le hK₀ hK₀0 Q
    _ = M * ENNReal.ofReal (16 * π * Lc K₀) * ∫⁻ Q in ball Q₀ 1, N2b Q := by
        rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top hM ENNReal.ofReal_ne_top),
          ← lintegral_indicator measurableSet_ball]
        refine lintegral_congr fun Q => ?_
        by_cases hQ : Q ∈ ball Q₀ 1 <;> simp [iQ, hQ, mul_assoc]
    _ ≤ M * ENNReal.ofReal (16 * π * Lc K₀) * ENNReal.ofReal (18 * π) := by
        gcongr
        exact setLIntegral_N2b_le Q₀
    _ = _ := by
        have hq := quadW_nonneg hK₂0 (by norm_num : (1 : ℝ) < 11 / 8)
          (by norm_num : (1 / 4 : ℝ) < 2 * (11 / 8) - 2)
        have h0 : 0 ≤ Mz K₁ K₂ := by unfold Mz; positivity
        rw [Msuf, ENNReal.ofReal_mul (mul_nonneg h0 (by have := Lc_pos hK₀0; positivity)),
          ENNReal.ofReal_mul h0]

end SLT.MiddlePositions.Two
