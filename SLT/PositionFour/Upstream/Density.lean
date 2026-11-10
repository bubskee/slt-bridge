/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Upstream.TwoCube

/-!
# Three cubes and the weighted density bound (note §1.2, step 4)

The interface statement `DensityBound β C` for `0 ≤ β < 2` (`exists_densityBound`).

1. **Tonelli against the third form** (`lintegral_rowMeasure_le`): by the permutation symmetry of
   the three forms and `TwoCubeBound`, `rowMeasure β ≤ (2/3) ρ̃_β · Lebesgue`, where
   `ρ̃_β(P) = ∫ ‖l‖^β |𝔇(P - l³)|^{-4/3} dl` (`rhoTilde`).
2. **Transport of the reference fibre** (`rhoTilde_le_of_twoCube`): for `P = l³ + m³ = g · P*`,
   the substitution `l = g · u` gives `ρ̃_β(P) ≤ (2 ‖g‖)^β |𝔇(P)|^{-1} ρ̃_β(P*)`, using
   `𝔇(g · Q) = det(g)⁶ 𝔇(Q)` and the source Jacobian `|det g|²`.
3. **The norm bound** `‖g‖ ≲ ‖P‖^{1/3} + ‖H(P)‖^{1/2} |𝔇(P)|^{-1/6}` (`norm_twoCube_cases`) and
   Sylvester's existence (`exists_twoCube_eq`) turn this into the note's equation (2):
   `ρ̃_β ≤ 4^β ρ̃_β(P*) · densityBound β` where `𝔇 ≠ 0` (`rhoTilde_le_densityBound`).

The measure-level statements avoid Radon–Nikodym derivatives: everything is an inequality between
lintegrals against test functions.
-/

@[expose] public section

namespace SLT.PositionFour

open MeasureTheory Set
open scoped ENNReal

/-! ### Tonelli against the third form -/

/-- The fibre integral `ρ̃_β(P) = ∫ ‖l‖^β |𝔇(P - l³)|^{-4/3} dl`. -/
noncomputable def rhoTilde (β : ℝ) (P : Cubic) : ℝ≥0∞ :=
  ∫⁻ l : Form, ENNReal.ofReal (‖l‖ ^ β) * twoCubeDensity (P - cube l)

/-- `cube` is measurable. -/
@[fun_prop] theorem measurable_cube : Measurable cube := by unfold cube; fun_prop

/-- `rowCubic` is measurable. -/
@[fun_prop] theorem measurable_rowCubic : Measurable rowCubic := by
  unfold rowCubic; fun_prop

/-- `ρ̃_β` is measurable. -/
@[fun_prop] theorem measurable_rhoTilde (β : ℝ) : Measurable (rhoTilde β) :=
  (by fun_prop : Measurable fun p : Cubic × Form =>
    ENNReal.ofReal (‖p.2‖ ^ β) * twoCubeDensity (p.1 - cube p.2)).lintegral_prod_right'

/-- Integrals against `rowMeasure`. -/
theorem lintegral_rowMeasure (β : ℝ) {φ : Cubic → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ P, φ P ∂(rowMeasure β) =
      ∫⁻ r, ENNReal.ofReal (rowWeight β r) * φ (rowCubic r) := by
  rw [rowMeasure, lintegral_map hφ measurable_rowCubic]
  exact lintegral_withDensity_eq_lintegral_mul _ (by unfold rowWeight; fun_prop)
    (hφ.comp measurable_rowCubic)

/-- Permutation symmetry: the weight on any one form integrates like the weight on the last. -/
theorem lintegral_weight_i_eq (β : ℝ) (φ : Cubic → ℝ≥0∞) (i : Fin 3) :
    ∫⁻ r : Row, ENNReal.ofReal (‖r i‖ ^ β) * φ (rowCubic r) =
      ∫⁻ r : Row, ENNReal.ofReal (‖r 2‖ ^ β) * φ (rowCubic r) := by
  set σ : Fin 3 ≃ Fin 3 := Equiv.swap i 2
  set e := MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => Form) σ
  have he : MeasurePreserving e := volume_measurePreserving_piCongrLeft (fun _ => Form) σ
  have h2 : ∀ r : Row, e r 2 = r i := fun r => by
    have := MeasurableEquiv.piCongrLeft_apply_apply σ (β := fun _ => Form) r i
    simpa [σ, Equiv.swap_apply_left] using this
  have hT : ∀ r : Row, rowCubic (e r) = rowCubic r := fun r => by
    simp only [rowCubic]
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [MeasurableEquiv.piCongrLeft_apply_apply σ (β := fun _ => Form) r b]
  calc ∫⁻ r : Row, ENNReal.ofReal (‖r i‖ ^ β) * φ (rowCubic r)
      = ∫⁻ r : Row, ENNReal.ofReal (‖e r 2‖ ^ β) * φ (rowCubic (e r)) :=
        lintegral_congr fun r => by rw [h2, hT]
    _ = _ := he.lintegral_comp_emb e.measurableEmbedding
      (fun r : Row => ENNReal.ofReal (‖r 2‖ ^ β) * φ (rowCubic r))

/-- The row cubic in the coordinates `((l₁, l₂), l₃)`. -/
theorem rowCubic_eq (r : Row) : rowCubic r = twoCube (r 0, r 1) + cube (r 2) := by
  simp [rowCubic, twoCube, Fin.sum_univ_three]

/-- **Tonelli against the third form.** For measurable `φ ≥ 0`,
`∫ φ ∂(rowMeasure β) ≤ 3 · (2/9) ∫ φ ρ̃_β`. -/
theorem lintegral_rowMeasure_le (β : ℝ) {φ : Cubic → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ P, φ P ∂(rowMeasure β) ≤ 3 * ENNReal.ofReal (2 / 9) * ∫⁻ P, φ P * rhoTilde β P := by
  rw [lintegral_rowMeasure β hφ]
  have hsplit : ∀ r : Row, ENNReal.ofReal (rowWeight β r) * φ (rowCubic r) =
      ∑ i, ENNReal.ofReal (‖r i‖ ^ β) * φ (rowCubic r) := fun r => by
    rw [rowWeight, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity), Finset.sum_mul]
  simp_rw [hsplit]
  rw [lintegral_finsetSum _ (fun i _ => by fun_prop)]
  simp_rw [lintegral_weight_i_eq β φ]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
    mul_assoc]
  gcongr
  -- the last form
  set G : (Form × Form) × Form → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (‖p.2‖ ^ β) * φ (twoCube p.1 + cube p.2)
  have hG : Measurable G := by simp only [G, twoCube]; fun_prop
  calc ∫⁻ r : Row, ENNReal.ofReal (‖r 2‖ ^ β) * φ (rowCubic r)
      = ∫⁻ r : Row, G (rowEquiv r) := by simp_rw [rowCubic_eq]; rfl
    _ = ∫⁻ p, G p := measurePreserving_rowEquiv.lintegral_comp_emb rowEquiv.measurableEmbedding _
    _ = ∫⁻ l : Form, ∫⁻ g : Form × Form, G (g, l) := by
        rw [Measure.volume_eq_prod, lintegral_prod_symm _ hG.aemeasurable]
    _ = ∫⁻ l : Form, ENNReal.ofReal (‖l‖ ^ β) * ∫⁻ g : Form × Form, φ (twoCube g + cube l) := by
        refine lintegral_congr fun l => ?_
        rw [← lintegral_const_mul _ (by unfold twoCube; fun_prop)]
    _ ≤ ∫⁻ l : Form, ENNReal.ofReal (‖l‖ ^ β) *
          (ENNReal.ofReal (2 / 9) * ∫⁻ P, φ (P + cube l) * twoCubeDensity P) := by
        gcongr with l
        exact lintegral_twoCube_le (φ := fun P => φ (P + cube l)) (by fun_prop)
    _ = ∫⁻ l : Form, ENNReal.ofReal (‖l‖ ^ β) *
          (ENNReal.ofReal (2 / 9) * ∫⁻ P, φ P * twoCubeDensity (P - cube l)) := by
        refine lintegral_congr fun l => ?_
        congr 2
        rw [← lintegral_sub_right_eq_self (fun P => φ (P + cube l) * twoCubeDensity P) (cube l)]
        simp
    _ = ENNReal.ofReal (2 / 9) * ∫⁻ P, φ P * rhoTilde β P := by
        set c := ENNReal.ofReal (2 / 9)
        have hF : Measurable (Function.uncurry fun (l : Form) (P : Cubic) =>
            ENNReal.ofReal (‖l‖ ^ β) * (φ P * twoCubeDensity (P - cube l))) := by
          change Measurable fun p : Form × Cubic =>
            ENNReal.ofReal (‖p.1‖ ^ β) * (φ p.2 * twoCubeDensity (p.2 - cube p.1))
          fun_prop
        calc ∫⁻ l : Form, ENNReal.ofReal (‖l‖ ^ β) *
              (c * ∫⁻ P, φ P * twoCubeDensity (P - cube l))
            = ∫⁻ l : Form, c * ∫⁻ P, ENNReal.ofReal (‖l‖ ^ β) *
                (φ P * twoCubeDensity (P - cube l)) := by
              refine lintegral_congr fun l => ?_
              rw [lintegral_const_mul _ (by fun_prop)]; ring
          _ = c * ∫⁻ l : Form, ∫⁻ P, ENNReal.ofReal (‖l‖ ^ β) *
                (φ P * twoCubeDensity (P - cube l)) :=
              lintegral_const_mul _ hF.lintegral_prod_right'
          _ = c * ∫⁻ P, ∫⁻ l : Form, ENNReal.ofReal (‖l‖ ^ β) *
                (φ P * twoCubeDensity (P - cube l)) := by
              rw [lintegral_lintegral_swap hF.aemeasurable]
          _ = c * ∫⁻ P, φ P * rhoTilde β P := by
              congr 1
              refine lintegral_congr fun P => ?_
              rw [rhoTilde, ← lintegral_const_mul _ (by fun_prop)]
              refine lintegral_congr fun l => ?_
              ring

/-! ### Transport of the reference fibre -/

/-- The bounding density is measurable. -/
@[fun_prop] theorem measurable_densityBound (β : ℝ) : Measurable (densityBound β) := by
  unfold densityBound disc hess; fun_prop

/-- `‖u₁ l + u₂ m‖ ≤ 2 ‖g‖ ‖u‖`. -/
theorem norm_formAct_le (g : Form × Form) (u : Form) : ‖formAct g u‖ ≤ 2 * ‖g‖ * ‖u‖ := by
  have ha : ‖g.1.1‖ ≤ ‖g‖ := (norm_fst_le g.1).trans (norm_fst_le g)
  have hb : ‖g.1.2‖ ≤ ‖g‖ := (norm_snd_le g.1).trans (norm_fst_le g)
  have hc : ‖g.2.1‖ ≤ ‖g‖ := (norm_fst_le g.2).trans (norm_snd_le g)
  have hd : ‖g.2.2‖ ≤ ‖g‖ := (norm_snd_le g.2).trans (norm_snd_le g)
  have h1 : ‖u.1‖ ≤ ‖u‖ := norm_fst_le u
  have h2 : ‖u.2‖ ≤ ‖u‖ := norm_snd_le u
  have hg := norm_nonneg g
  rw [formAct, Prod.norm_def]
  refine max_le ?_ ?_
  · calc ‖u.1 * g.1.1 + u.2 * g.2.1‖ ≤ ‖u.1‖ * ‖g.1.1‖ + ‖u.2‖ * ‖g.2.1‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ ‖u‖ * ‖g‖ + ‖u‖ * ‖g‖ := by gcongr
      _ = 2 * ‖g‖ * ‖u‖ := by ring
  · calc ‖u.1 * g.1.2 + u.2 * g.2.2‖ ≤ ‖u.1‖ * ‖g.1.2‖ + ‖u.2‖ * ‖g.2.2‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ ‖u‖ * ‖g‖ + ‖u‖ * ‖g‖ := by gcongr
      _ = 2 * ‖g‖ * ‖u‖ := by ring

/-- Covariance of the two-cube density: `|𝔇(g · Q)|^{-4/3} = |det g|^{-8} |𝔇(Q)|^{-4/3}`. -/
theorem twoCubeDensity_cubicAct (g : Form × Form) (hg : det2 g ≠ 0) (Q : Cubic) :
    twoCubeDensity (cubicAct g Q) = ‖det2 g‖ₑ ^ (-(8 : ℝ)) * twoCubeDensity Q := by
  have h6 : (‖det2 g ^ 6‖₊ : ℝ≥0∞) ≠ 0 := by simpa using pow_ne_zero 6 hg
  simp only [twoCubeDensity]
  rw [disc_cubicAct, nnnorm_mul, ENNReal.coe_mul, ENNReal.mul_inv (Or.inl h6) (Or.inl (by simp)),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  congr 1
  rw [inv_nnnorm_rpow, enorm_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- **Transport.** For `P = l³ + m³` with `det(l, m) ≠ 0`,
`ρ̃_β(P) ≤ |𝔇(P)|^{-1} (2 ‖g‖)^β ρ̃_β(P*)`. -/
theorem rhoTilde_le_of_twoCube {β : ℝ} (hβ : 0 ≤ β) (g : Form × Form) (hg : det2 g ≠ 0) :
    rhoTilde β (twoCube g) ≤
      (‖disc (twoCube g)‖₊ : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((2 * ‖g‖) ^ β) * refFibre β := by
  set F : Form → ℝ≥0∞ := fun l => ENNReal.ofReal (‖l‖ ^ β) * twoCubeDensity (twoCube g - cube l)
  have hF : Measurable F := by simp only [F, twoCube]; fun_prop
  have hsub := lintegral_comp_formAct g hg hF
  have hn0 : ENNReal.ofReal (Complex.normSq (det2 g)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Complex.normSq_pos.mpr hg)
  have hrho : rhoTilde β (twoCube g) =
      ENNReal.ofReal (Complex.normSq (det2 g)) * ∫⁻ u, F (formAct g u) := by
    rw [hsub, ← mul_assoc, ENNReal.mul_inv_cancel hn0 ENNReal.ofReal_ne_top, one_mul]; rfl
  have hpt : ∀ u, F (formAct g u) ≤ ‖det2 g‖ₑ ^ (-(8 : ℝ)) * ENNReal.ofReal ((2 * ‖g‖) ^ β) *
      (ENNReal.ofReal (‖u‖ ^ β) * twoCubeDensity (refCubic - cube u)) := by
    intro u
    simp only [F]
    rw [twoCube_sub_cube_formAct, twoCubeDensity_cubicAct g hg]
    have hw : ENNReal.ofReal (‖formAct g u‖ ^ β) ≤
        ENNReal.ofReal ((2 * ‖g‖) ^ β) * ENNReal.ofReal (‖u‖ ^ β) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (norm_nonneg _) (norm_formAct_le g u) hβ)
    calc ENNReal.ofReal (‖formAct g u‖ ^ β) *
          (‖det2 g‖ₑ ^ (-(8 : ℝ)) * twoCubeDensity (refCubic - cube u))
        ≤ (ENNReal.ofReal ((2 * ‖g‖) ^ β) * ENNReal.ofReal (‖u‖ ^ β)) *
          (‖det2 g‖ₑ ^ (-(8 : ℝ)) * twoCubeDensity (refCubic - cube u)) := by gcongr
      _ = _ := by ring
  have hD : ‖det2 g‖ₑ ≠ 0 := enorm_ne_zero.mpr hg
  have hpow : ENNReal.ofReal (Complex.normSq (det2 g)) * ‖det2 g‖ₑ ^ (-(8 : ℝ)) =
      (‖disc (twoCube g)‖₊ : ℝ≥0∞)⁻¹ := by
    rw [Complex.normSq_eq_norm_sq, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_add _ _ hD enorm_ne_top, disc_twoCube,
      ← ENNReal.rpow_one ((‖det2 g ^ 6‖₊ : ℝ≥0∞)⁻¹), inv_nnnorm_rpow, enorm_pow,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc rhoTilde β (twoCube g) = ENNReal.ofReal (Complex.normSq (det2 g)) * ∫⁻ u, F (formAct g u) :=
        hrho
    _ ≤ ENNReal.ofReal (Complex.normSq (det2 g)) * ∫⁻ u, ‖det2 g‖ₑ ^ (-(8 : ℝ)) *
          ENNReal.ofReal ((2 * ‖g‖) ^ β) *
          (ENNReal.ofReal (‖u‖ ^ β) * twoCubeDensity (refCubic - cube u)) := by
        gcongr with u; exact hpt u
    _ = (‖disc (twoCube g)‖₊ : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((2 * ‖g‖) ^ β) * refFibre β := by
        rw [lintegral_const_mul _ (by fun_prop), ← hpow, refFibre]; ring

/-- The real form of the norm bound: `(2 ‖g‖)^β ≤ 4^β (‖P‖^{β/3} + ‖H(P)‖^{β/2} |𝔇(P)|^{-β/6})`
for `P = l³ + m³` with `det(l, m) ≠ 0`. -/
theorem two_norm_rpow_le {β : ℝ} (hβ : 0 ≤ β) (g : Form × Form) (hg : det2 g ≠ 0) :
    (2 * ‖g‖) ^ β ≤ 4 ^ β * (‖twoCube g‖ ^ (β / 3) +
      ‖hess (twoCube g)‖ ^ (β / 2) * ‖disc (twoCube g)‖ ^ (-(β / 6))) := by
  have hG := norm_nonneg g
  have hP := norm_nonneg (twoCube g)
  have hH := norm_nonneg (hess (twoCube g))
  have hDpos : 0 < ‖det2 g‖ := norm_pos_iff.mpr hg
  have hdisc : ‖disc (twoCube g)‖ = ‖det2 g‖ ^ 6 := by rw [disc_twoCube, norm_pow]
  have hA : 0 ≤ ‖twoCube g‖ ^ (β / 3) := by positivity
  have hB : 0 ≤ ‖hess (twoCube g)‖ ^ (β / 2) * ‖disc (twoCube g)‖ ^ (-(β / 6)) := by positivity
  rcases norm_twoCube_cases g with h | h
  · -- `2 ‖g‖ ≤ 4 ‖P‖^{1/3}`
    have hc : 2 * ‖g‖ ≤ 4 * ‖twoCube g‖ ^ (1 / 3 : ℝ) := by
      refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp
        ?_
      rw [mul_pow, mul_pow, ← Real.rpow_natCast (‖twoCube g‖ ^ (1 / 3 : ℝ)), ← Real.rpow_mul hP]
      norm_num
      nlinarith
    calc (2 * ‖g‖) ^ β ≤ (4 * ‖twoCube g‖ ^ (1 / 3 : ℝ)) ^ β :=
          Real.rpow_le_rpow (by positivity) hc hβ
      _ = 4 ^ β * ‖twoCube g‖ ^ (β / 3) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hP]; ring_nf
      _ ≤ _ := by gcongr; linarith
  · -- `2 ‖g‖ ≤ 4 ‖H‖^{1/2} / |det g|`
    have hc : 2 * ‖g‖ * ‖det2 g‖ ≤ 4 * ‖hess (twoCube g)‖ ^ (1 / 2 : ℝ) := by
      refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp
        ?_
      rw [mul_pow, mul_pow, mul_pow, ← Real.rpow_natCast (‖hess (twoCube g)‖ ^ (1 / 2 : ℝ)),
        ← Real.rpow_mul hH]
      norm_num
      nlinarith
    have hc' : 2 * ‖g‖ ≤ 4 * ‖hess (twoCube g)‖ ^ (1 / 2 : ℝ) * ‖det2 g‖ ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv, le_div_iff₀ hDpos]; exact hc
    calc (2 * ‖g‖) ^ β
        ≤ (4 * ‖hess (twoCube g)‖ ^ (1 / 2 : ℝ) * ‖det2 g‖ ^ (-1 : ℝ)) ^ β :=
          Real.rpow_le_rpow (by positivity) hc' hβ
      _ = 4 ^ β * (‖hess (twoCube g)‖ ^ (β / 2) * ‖disc (twoCube g)‖ ^ (-(β / 6))) := by
          rw [Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hH,
            ← Real.rpow_mul hDpos.le, hdisc, ← Real.rpow_natCast (‖det2 g‖) 6,
            ← Real.rpow_mul hDpos.le]
          ring_nf
      _ ≤ _ := by gcongr; linarith

/-- **The note's equation (2) where `𝔇 ≠ 0`.** `ρ̃_β ≤ 4^β ρ̃_β(P*) · densityBound β`. -/
theorem rhoTilde_le_densityBound {β : ℝ} (hβ : 0 ≤ β) (P : Cubic) (hP : disc P ≠ 0) :
    rhoTilde β P ≤ ENNReal.ofReal (4 ^ β) * refFibre β * densityBound β P := by
  obtain ⟨g, rfl⟩ := exists_twoCube_eq P hP
  have hg : det2 g ≠ 0 := by
    intro h; apply hP; rw [disc_twoCube, h]; ring
  refine (rhoTilde_le_of_twoCube hβ g hg).trans ?_
  set δ := (‖disc (twoCube g)‖₊ : ℝ≥0∞)⁻¹
  have hδ0 : δ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
  have hδt : δ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by simpa using hP)
  have hdpos : 0 < ‖disc (twoCube g)‖ := norm_pos_iff.mpr hP
  have hreal := two_norm_rpow_le hβ g hg
  have hpow : ENNReal.ofReal (‖disc (twoCube g)‖ ^ (-(β / 6))) = δ ^ (β / 6) := by
    rw [← ENNReal.ofReal_rpow_of_pos hdpos, ofReal_norm, ENNReal.rpow_neg, ← ENNReal.inv_rpow]
    rfl
  have h16 : δ ^ (1 + β / 6) = δ * δ ^ (β / 6) := by
    rw [ENNReal.rpow_add _ _ hδ0 hδt, ENNReal.rpow_one]
  calc δ * ENNReal.ofReal ((2 * ‖g‖) ^ β) * refFibre β
      ≤ δ * (ENNReal.ofReal (4 ^ β) * (ENNReal.ofReal (‖twoCube g‖ ^ (β / 3)) +
          ENNReal.ofReal (‖hess (twoCube g)‖ ^ (β / 2)) *
            ENNReal.ofReal (‖disc (twoCube g)‖ ^ (-(β / 6))))) * refFibre β := by
        gcongr
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (4 ^ β) * refFibre β * densityBound β (twoCube g) := by
        rw [densityBound, hpow, h16]; ring

/-! ### The interface statement -/

/-- The constant of `DensityBound`: `3 · (2/9) · (4^β ρ̃_β(P*) + 1)`. -/
noncomputable def densityConst (β : ℝ) : ℝ := 3 * (2 / 9) * (4 ^ β * (refFibre β).toReal + 1)

/-- **Interface, part 1, proved.** For `0 ≤ β < 2`, `DensityBound β (densityConst β)`. -/
theorem densityBound_holds {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 2) :
    DensityBound β (densityConst β) := by
  have hfin := refFibre_lt_top hβ0 hβ
  set Cρ : ℝ := 4 ^ β * (refFibre β).toReal + 1
  have hCρ : 0 < Cρ := by positivity
  -- the pointwise bound away from `0`
  have hpt : ∀ P : Cubic, P ≠ 0 → rhoTilde β P ≤ ENNReal.ofReal Cρ * densityBound β P := by
    intro P hP0
    by_cases hP : disc P = 0
    · have hdb : densityBound β P = ⊤ := by
        have : ENNReal.ofReal (‖P‖ ^ (β / 3)) ≠ 0 :=
          ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos (norm_pos_iff.mpr hP0) _)
        simp [densityBound, hP, this]
      rw [hdb, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hCρ)]
      exact le_top
    · refine (rhoTilde_le_densityBound hβ0 P hP).trans ?_
      gcongr
      rw [← ENNReal.ofReal_toReal hfin.ne, ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [Measure.smul_apply, withDensity_apply _ hA, smul_eq_mul]
  have h := lintegral_rowMeasure_le β (φ := A.indicator 1) (measurable_one.indicator hA)
  rw [lintegral_indicator_one hA] at h
  refine h.trans ?_
  have hmono : ∫⁻ P, A.indicator 1 P * rhoTilde β P ≤
      ENNReal.ofReal Cρ * ∫⁻ P in A, densityBound β P := by
    rw [← lintegral_indicator hA, ← lintegral_const_mul _
      ((measurable_densityBound β).indicator hA)]
    refine lintegral_mono_ae ?_
    filter_upwards [Measure.ae_ne volume (0 : Cubic)] with P hP
    by_cases hPA : P ∈ A
    · simp only [indicator_of_mem hPA, Pi.one_apply, one_mul]; exact hpt P hP
    · simp [indicator_of_notMem hPA]
  calc 3 * ENNReal.ofReal (2 / 9) * ∫⁻ P, A.indicator 1 P * rhoTilde β P
      ≤ 3 * ENNReal.ofReal (2 / 9) * (ENNReal.ofReal Cρ * ∫⁻ P in A, densityBound β P) := by
        gcongr
    _ = ENNReal.ofReal (densityConst β) * ∫⁻ P in A, densityBound β P := by
        rw [densityConst, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
        simp [Cρ, mul_assoc]

/-- **Interface, part 1.** For `0 ≤ β < 2` there is a constant with `DensityBound β C`. -/
theorem exists_densityBound {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 2) : ∃ C, DensityBound β C :=
  ⟨_, densityBound_holds hβ0 hβ⟩

end SLT.PositionFour
