/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Upstream.Algebra
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Sylvester's two-cube theorem for binary cubics (note §1)

* `exists_twoCube_eq` (existence): every cubic with `𝔇(P) ≠ 0` is `l³ + m³`;
* `twoCube_eq_twoCube` (uniqueness): if `l'³ + m'³ = l³ + m³` with `det(l, m) ≠ 0`, then
  `(l', m')` is `(ζ₁ l, ζ₂ m)` or `(ζ₁ m, ζ₂ l)` with `ζᵢ³ = 1`;
* `exists_finset_twoCube_fibre`: hence the fibre of the two-cube map over a point, restricted to
  `det ≠ 0`, has at most `18` elements;
* `norm_twoCube_cases` (the note's norm bound for a two-cube representation): either
  `‖g‖³ ≤ 2 ‖P‖` or `‖g‖² |det g|² ≤ 4 ‖H(P)‖`, for `P = l³ + m³`.

Norms are the sup norms of `Defs.lean`.
-/

@[expose] public section

namespace SLT.PositionFour

/-! ### Existence -/

/-- The inverse substitution `((d, -b), (-c, a)) / det`. -/
noncomputable def invPair (g : Form × Form) : Form × Form :=
  ((g.2.2 / det2 g, -g.1.2 / det2 g), (-g.2.1 / det2 g, g.1.1 / det2 g))

/-- `g · (g⁻¹ · P) = P`. -/
theorem cubicAct_invPair (g : Form × Form) (hg : det2 g ≠ 0) (P : Cubic) :
    cubicAct g (cubicAct (invPair g) P) = P := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := g
  simp only [det2] at hg
  ext i
  fin_cases i <;>
    · simp only [cubicAct, invPair, det2, Matrix.cons_val, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
      generalize hD : a * d - b * c = D at hg ⊢
      field_simp
      subst hD
      ring

/-- `g⁻¹ · (g · h) = h` on quadratics. -/
theorem quadAct_invPair (g : Form × Form) (hg : det2 g ≠ 0) (h : Fin 3 → ℂ) :
    quadAct (invPair g) (quadAct g h) = h := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := g
  simp only [det2] at hg
  ext i
  fin_cases i <;>
    · simp only [quadAct, invPair, det2, Matrix.cons_val, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
      generalize hD : a * d - b * c = D at hg ⊢
      field_simp
      subst hD
      ring

/-- Substitution on quadratics is homogeneous. -/
theorem quadAct_smul (g : Form × Form) (c : ℂ) (h : Fin 3 → ℂ) :
    quadAct g (c • h) = c • quadAct g h := by
  ext i
  fin_cases i <;> simp [quadAct] <;> ring

/-- The Hessian of a cubic with `𝔇 ≠ 0` factors as `κ l m` with `det(l, m) ≠ 0`, `κ ≠ 0`. -/
theorem exists_hess_factor (P : Cubic) (hP : disc P ≠ 0) :
    ∃ g : Form × Form, ∃ κ : ℂ, det2 g ≠ 0 ∧ κ ≠ 0 ∧ hess P = κ • formMul g.1 g.2 := by
  have hD := disc_eq_hess P
  generalize hess P = h at hD ⊢
  by_cases h00 : h 0 = 0
  · refine ⟨((0, 1), (h 1, h 2)), 1, ?_, one_ne_zero, ?_⟩
    · have : h 1 ≠ 0 := by intro h'; apply hP; rw [hD, h', h00]; ring
      simpa [det2] using this
    · ext i
      fin_cases i <;> simp [formMul, h00]
  · obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (disc P) two_pos
    have hδ0 : δ ≠ 0 := by rintro rfl; apply hP; rw [← hδ]; ring
    refine ⟨((2 * h 0, h 1 - δ), (2 * h 0, h 1 + δ)), 1 / (4 * h 0), ?_, by simpa using h00, ?_⟩
    · simp only [det2]
      intro h'
      apply mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) h00) hδ0
      linear_combination h'
    · rw [hD] at hδ
      ext i
      fin_cases i <;> simp [formMul] <;> field_simp
      · ring
      · ring
      · linear_combination hδ

/-- A cubic whose Hessian is a nonzero multiple of `s t` has no middle coefficients. -/
theorem middle_eq_zero_of_hess (Q : Cubic) (h0 : hess Q 0 = 0) (h1 : hess Q 1 ≠ 0)
    (h2 : hess Q 2 = 0) : Q 1 = 0 ∧ Q 2 = 0 := by
  simp only [hess, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2
  by_cases hQ1 : Q 1 = 0
  · refine ⟨hQ1, ?_⟩
    have : Q 2 ^ 2 = 0 := by rw [hQ1] at h2; linear_combination -h2
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  · exfalso
    have hQ2 : Q 2 ≠ 0 := by
      rintro h; apply hQ1; have : Q 1 ^ 2 = 0 := by rw [h] at h0; linear_combination -h0
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    apply h1
    have : (Q 0 * Q 3 - Q 1 * Q 2) * (Q 1 * Q 2) = 0 := by
      linear_combination (Q 1 * Q 3) * h0 + (Q 1 ^ 2) * h2
    exact (mul_eq_zero.mp this).resolve_right (mul_ne_zero hQ1 hQ2)

/-- **Sylvester, existence.** Every cubic with `𝔇(P) ≠ 0` is a sum of two cubes. -/
theorem exists_twoCube_eq (P : Cubic) (hP : disc P ≠ 0) : ∃ g : Form × Form, twoCube g = P := by
  obtain ⟨g, κ, hg, hκ, hH⟩ := exists_hess_factor P hP
  set Q := cubicAct (invPair g) P
  have hPQ : cubicAct g Q = P := cubicAct_invPair g hg P
  -- `det(g)² H(Q) = κ s t`
  have key : det2 g ^ 2 • hess Q = κ • ![0, 1, 0] := by
    have h1 : quadAct g (det2 g ^ 2 • hess Q) = quadAct g (κ • ![0, 1, 0]) := by
      rw [quadAct_smul, quadAct_smul, quadAct_st, ← hH, ← hess_cubicAct, hPQ]
    have := congrArg (quadAct (invPair g)) h1
    rwa [quadAct_invPair g hg, quadAct_invPair g hg] at this
  have hd : det2 g ^ 2 ≠ 0 := pow_ne_zero 2 hg
  have k0 := congrFun key 0
  have k1 := congrFun key 1
  have k2 := congrFun key 2
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_zero, mul_one] at k0 k1 k2
  have hQ0 : hess Q 0 = 0 := (mul_eq_zero.mp k0).resolve_left hd
  have hQ2 : hess Q 2 = 0 := (mul_eq_zero.mp k2).resolve_left hd
  have hQ1 : hess Q 1 ≠ 0 := by intro h; rw [h, mul_zero] at k1; exact hκ k1.symm
  obtain ⟨hm1, hm2⟩ := middle_eq_zero_of_hess Q hQ0 hQ1 hQ2
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (Q 0) (by norm_num : 0 < 3)
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (Q 3) (by norm_num : 0 < 3)
  refine ⟨((α * g.1.1, α * g.1.2), (β * g.2.1, β * g.2.2)), ?_⟩
  rw [← hPQ]
  ext i
  fin_cases i <;> simp [twoCube, cube, cubicAct, hm1, hm2, ← hα, ← hβ] <;> ring

/-! ### Uniqueness and the fibre bound -/

/-- If `det(l, m) ≠ 0`, the cubes `l³` and `m³` are linearly independent. -/
theorem cube_independent (g : Form × Form) (hg : det2 g ≠ 0) {α β : ℂ}
    (h : α • cube g.1 + β • cube g.2 = 0) : α = 0 ∧ β = 0 := by
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  have e3 := congrFun h 3
  simp only [cube, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val,
    Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at e0 e1 e2 e3
  have hd3 : det2 g ^ 3 ≠ 0 := pow_ne_zero 3 hg
  set a := g.1.1; set b := g.1.2; set c := g.2.1; set d := g.2.2
  constructor
  · have : α * det2 g ^ 3 = 0 := by
      simp only [det2]
      linear_combination d ^ 3 * e0 - 3 * c * d ^ 2 * e1 + 3 * c ^ 2 * d * e2 - c ^ 3 * e3
    exact (mul_eq_zero.mp this).resolve_right hd3
  · have : β * det2 g ^ 3 = 0 := by
      simp only [det2]
      linear_combination -(b ^ 3 * e0 - 3 * a * b ^ 2 * e1 + 3 * a ^ 2 * b * e2 - a ^ 3 * e3)
    exact (mul_eq_zero.mp this).resolve_right hd3

/-- A form `l'` with `l'(b, -a) = 0` is a multiple of `l = (a, b) ≠ 0`. -/
theorem exists_smul_of_cross_eq_zero {l l' : Form} (hl : l ≠ 0)
    (h : l'.1 * l.2 - l'.2 * l.1 = 0) : ∃ c : ℂ, l' = c • l := by
  by_cases h1 : l.1 = 0
  · have h2 : l.2 ≠ 0 := by
      intro h2; apply hl; exact Prod.ext h1 h2
    refine ⟨l'.2 / l.2, Prod.ext ?_ ?_⟩
    · simp only [Prod.smul_fst, smul_eq_mul]; rw [h1, mul_zero]
      have : l'.1 * l.2 = 0 := by rw [h1, mul_zero] at h; linear_combination h
      exact (mul_eq_zero.mp this).resolve_right h2
    · simp only [Prod.smul_snd, smul_eq_mul]; field_simp
  · refine ⟨l'.1 / l.1, Prod.ext ?_ ?_⟩
    · simp only [Prod.smul_fst, smul_eq_mul]; field_simp
    · simp only [Prod.smul_snd, smul_eq_mul]; field_simp; linear_combination -h

/-- The left form of a pair with `det ≠ 0` is nonzero. -/
theorem fst_ne_zero_of_det2 {g : Form × Form} (hg : det2 g ≠ 0) : g.1 ≠ 0 := by
  intro h; apply hg; simp [det2, h]

/-- The right form of a pair with `det ≠ 0` is nonzero. -/
theorem snd_ne_zero_of_det2 {g : Form × Form} (hg : det2 g ≠ 0) : g.2 ≠ 0 := by
  intro h; apply hg; simp [det2, h]

/-- The scaled pair `(ζ₁ l, ζ₂ m)`, or its swap `(ζ₁ m, ζ₂ l)`. -/
def scalePair (g : Form × Form) (z : (ℂ × ℂ) × Bool) : Form × Form :=
  if z.2 then (z.1.1 • g.1, z.1.2 • g.2) else (z.1.1 • g.2, z.1.2 • g.1)

/-- **Sylvester, uniqueness.** If `l'³ + m'³ = l³ + m³` and `det(l, m) ≠ 0`, then
`(l', m') = (ζ₁ l, ζ₂ m)` or `(ζ₁ m, ζ₂ l)` with `ζ₁³ = ζ₂³ = 1`. -/
theorem twoCube_eq_twoCube {g g' : Form × Form} (hg : det2 g ≠ 0)
    (h : twoCube g' = twoCube g) :
    ∃ z : (ℂ × ℂ) × Bool, z.1.1 ^ 3 = 1 ∧ z.1.2 ^ 3 = 1 ∧ g' = scalePair g z := by
  have hg' : det2 g' ≠ 0 := by
    intro h0; apply pow_ne_zero 6 hg; rw [← disc_twoCube, ← h, disc_twoCube, h0]; ring
  have hH := congrArg hess h
  rw [hess_twoCube, hess_twoCube] at hH
  have q0 := congrFun hH 0
  have q1 := congrFun hH 1
  have q2 := congrFun hH 2
  simp only [formMul, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one] at q0 q1 q2
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := g
  obtain ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ := g'
  simp only at q0 q1 q2
  have hd' : det2 ((a', b'), (c', d')) ^ 2 ≠ 0 := pow_ne_zero 2 hg'
  -- evaluate the Hessian identity at the roots `(b, -a)` of `l` and `(d, -c)` of `m`
  have rl : (a' * b - b' * a) * (c' * b - d' * a) = 0 := by
    have : det2 ((a', b'), (c', d')) ^ 2 * ((a' * b - b' * a) * (c' * b - d' * a)) = 0 := by
      linear_combination b ^ 2 * q0 - a * b * q1 + a ^ 2 * q2
    exact (mul_eq_zero.mp this).resolve_left hd'
  have rm : (a' * d - b' * c) * (c' * d - d' * c) = 0 := by
    have : det2 ((a', b'), (c', d')) ^ 2 * ((a' * d - b' * c) * (c' * d - d' * c)) = 0 := by
      linear_combination d ^ 2 * q0 - c * d * q1 + c ^ 2 * q2
    exact (mul_eq_zero.mp this).resolve_left hd'
  have hl : ((a, b) : Form) ≠ 0 := fst_ne_zero_of_det2 hg
  have hm : ((c, d) : Form) ≠ 0 := snd_ne_zero_of_det2 hg
  simp only [det2] at hg hg'
  -- a form cannot be parallel to both `l` and `m`
  have no_both : ∀ x y : ℂ, x * b - y * a = 0 → x * d - y * c = 0 → x = 0 ∧ y = 0 := by
    intro x y h1 h2
    constructor
    · have : x * (a * d - b * c) = 0 := by linear_combination -(c * h1) + a * h2
      exact (mul_eq_zero.mp this).resolve_right hg
    · have : y * (a * d - b * c) = 0 := by linear_combination -(d * h1) + b * h2
      exact (mul_eq_zero.mp this).resolve_right hg
  have hcube := h
  simp only [twoCube] at hcube
  rcases mul_eq_zero.mp rl with hA | hB <;> rcases mul_eq_zero.mp rm with hC | hD
  · obtain ⟨rfl, rfl⟩ := no_both a' b' hA hC; exfalso; apply hg'; ring
  · -- `l' ∥ l`, `m' ∥ m`
    obtain ⟨c₁, hc₁⟩ := exists_smul_of_cross_eq_zero hl (l' := (a', b')) (by simpa using hA)
    obtain ⟨c₂, hc₂⟩ := exists_smul_of_cross_eq_zero hm (l' := (c', d')) (by simpa using hD)
    have : (c₁ ^ 3 - 1) • cube (a, b) + (c₂ ^ 3 - 1) • cube (c, d) = 0 := by
      rw [hc₁, hc₂] at hcube
      ext i
      have := congrFun hcube i
      fin_cases i <;> simp [cube] at this ⊢ <;> linear_combination this
    obtain ⟨h1, h2⟩ := cube_independent ((a, b), (c, d)) (by simpa [det2] using hg) this
    refine ⟨((c₁, c₂), true), by linear_combination h1, by linear_combination h2, ?_⟩
    simp [scalePair, hc₁, hc₂]
  · -- `m' ∥ l`, `l' ∥ m`
    obtain ⟨c₁, hc₁⟩ := exists_smul_of_cross_eq_zero hm (l' := (a', b')) (by simpa using hC)
    obtain ⟨c₂, hc₂⟩ := exists_smul_of_cross_eq_zero hl (l' := (c', d')) (by simpa using hB)
    have : (c₂ ^ 3 - 1) • cube (a, b) + (c₁ ^ 3 - 1) • cube (c, d) = 0 := by
      rw [hc₁, hc₂] at hcube
      ext i
      have := congrFun hcube i
      fin_cases i <;> simp [cube] at this ⊢ <;> linear_combination this
    obtain ⟨h1, h2⟩ := cube_independent ((a, b), (c, d)) (by simpa [det2] using hg) this
    refine ⟨((c₁, c₂), false), by linear_combination h2, by linear_combination h1, ?_⟩
    simp [scalePair, hc₁, hc₂]
  · obtain ⟨rfl, rfl⟩ := no_both c' d' hB hD; exfalso; apply hg'; ring

open Classical in
/-- **The fibre bound.** Over any cubic, the two-cube map has at most `18` preimages with
`det ≠ 0`. -/
theorem exists_finset_twoCube_fibre (P : Cubic) :
    ∃ F : Finset (Form × Form), F.card ≤ 18 ∧
      ∀ g, det2 g ≠ 0 → twoCube g = P → g ∈ F := by
  by_cases hex : ∃ g₀, det2 g₀ ≠ 0 ∧ twoCube g₀ = P
  · obtain ⟨g₀, hg₀, hP⟩ := hex
    let R := Polynomial.nthRootsFinset 3 (1 : ℂ)
    have hR : R.card ≤ 3 :=
      (Multiset.toFinset_card_le _).trans (by
        convert Polynomial.card_nthRoots 3 (1 : ℂ))
    refine ⟨((R ×ˢ R) ×ˢ Finset.univ).image (scalePair g₀), ?_, ?_⟩
    · refine Finset.card_image_le.trans ?_
      rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_bool]
      calc R.card * R.card * 2 ≤ 3 * 3 * 2 := by gcongr
        _ = 18 := by norm_num
    · intro g _ hg
      obtain ⟨z, hz1, hz2, rfl⟩ := twoCube_eq_twoCube hg₀ (hg.trans hP.symm)
      refine Finset.mem_image.mpr ⟨z, ?_, rfl⟩
      simp [R, Polynomial.mem_nthRootsFinset, hz1, hz2]
  · refine ⟨∅, by simp, fun g hg hP => (hex ⟨g, hg, hP⟩).elim⟩

/-! ### The norm bound -/

/-- `‖l³‖ = ‖l‖³` for the sup norms. -/
theorem norm_cube (l : Form) : ‖cube l‖ = ‖l‖ ^ 3 := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    have ha : ‖l.1‖ ≤ ‖l‖ := norm_fst_le l
    have hb : ‖l.2‖ ≤ ‖l‖ := norm_snd_le l
    fin_cases i <;> simp only [cube, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_one, norm_mul, norm_pow]
    · exact pow_le_pow_left₀ (norm_nonneg _) ha 3
    · calc ‖l.1‖ ^ 2 * ‖l.2‖ ≤ ‖l‖ ^ 2 * ‖l‖ := by gcongr
        _ = ‖l‖ ^ 3 := by ring
    · calc ‖l.1‖ * ‖l.2‖ ^ 2 ≤ ‖l‖ * ‖l‖ ^ 2 := by gcongr
        _ = ‖l‖ ^ 3 := by ring
    · exact pow_le_pow_left₀ (norm_nonneg _) hb 3
  · have h0 := norm_le_pi_norm (cube l) 0
    have h3 := norm_le_pi_norm (cube l) 3
    simp only [cube, Matrix.cons_val, Matrix.cons_val_zero, norm_pow] at h0 h3
    rw [Prod.norm_def]
    rcases le_total ‖l.1‖ ‖l.2‖ with h | h
    · rw [max_eq_right h]; exact h3
    · rw [max_eq_left h]; exact h0

/-- `‖l m‖ ≥ ‖l‖ ‖m‖ / 2` for the sup norms. -/
theorem norm_mul_le_two_norm_formMul (l m : Form) : ‖l‖ * ‖m‖ ≤ 2 * ‖formMul l m‖ := by
  have hX : ‖l.1 * m.1‖ ≤ ‖formMul l m‖ := norm_le_pi_norm (formMul l m) 0
  have hY : ‖l.1 * m.2 + l.2 * m.1‖ ≤ ‖formMul l m‖ := norm_le_pi_norm (formMul l m) 1
  have hZ : ‖l.2 * m.2‖ ≤ ‖formMul l m‖ := norm_le_pi_norm (formMul l m) 2
  have hY1 : ‖l.1 * m.2‖ ≤ ‖l.1 * m.2 + l.2 * m.1‖ + ‖l.2 * m.1‖ := by
    simpa using norm_sub_le (l.1 * m.2 + l.2 * m.1) (l.2 * m.1)
  have hY2 : ‖l.2 * m.1‖ ≤ ‖l.1 * m.2 + l.2 * m.1‖ + ‖l.1 * m.2‖ := by
    simpa using norm_sub_le (l.1 * m.2 + l.2 * m.1) (l.1 * m.2)
  rw [norm_mul] at hX hZ hY1 hY2
  rw [norm_mul] at hY1 hY2
  rw [Prod.norm_def, Prod.norm_def]
  have := norm_nonneg l.1; have := norm_nonneg l.2
  have := norm_nonneg m.1; have := norm_nonneg m.2
  rcases le_total ‖l.1‖ ‖l.2‖ with h1 | h1 <;> rcases le_total ‖m.1‖ ‖m.2‖ with h2 | h2
  · rw [max_eq_right h1, max_eq_right h2]; nlinarith
  · rw [max_eq_right h1, max_eq_left h2]
    nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg m.2)]
  · rw [max_eq_left h1, max_eq_right h2]
    nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg m.1)]
  · rw [max_eq_left h1, max_eq_left h2]; nlinarith

/-- `‖H(P)‖ = |det g|² ‖l m‖` for `P = l³ + m³`. -/
theorem norm_hess_twoCube (g : Form × Form) :
    ‖hess (twoCube g)‖ = ‖det2 g‖ ^ 2 * ‖formMul g.1 g.2‖ := by
  rw [hess_twoCube, norm_smul, norm_pow]

/-- The product of forms is commutative. -/
theorem formMul_comm (l m : Form) : formMul l m = formMul m l := by
  ext i
  fin_cases i <;> simp [formMul] <;> ring

/-- **The norm bound** for a two-cube representation `P = l³ + m³`: either `‖g‖³ ≤ 2 ‖P‖`, or
`‖g‖² |det g|² ≤ 4 ‖H(P)‖`. With `|det g| = |𝔇(P)|^{1/6}` this is the note's
`‖g‖ ≲ ‖P‖^{1/3} + ‖H(P)‖^{1/2} |𝔇(P)|^{-1/6}`. -/
theorem norm_twoCube_cases (g : Form × Form) :
    ‖g‖ ^ 3 ≤ 2 * ‖twoCube g‖ ∨ ‖g‖ ^ 2 * ‖det2 g‖ ^ 2 ≤ 4 * ‖hess (twoCube g)‖ := by
  -- the case `‖m‖ ≤ ‖l‖`; the other follows by symmetry
  have key : ∀ l m : Form, ‖m‖ ≤ ‖l‖ →
      ‖l‖ ^ 3 ≤ 2 * ‖cube l + cube m‖ ∨ ‖l‖ ^ 2 ≤ 4 * ‖formMul l m‖ := by
    intro l m hml
    have hL := norm_nonneg l
    have hM := norm_nonneg m
    by_cases hc : 2 * ‖m‖ ^ 3 ≤ ‖l‖ ^ 3
    · left
      have h1 : ‖cube l‖ ≤ ‖cube l + cube m‖ + ‖cube m‖ := by
        simpa using norm_sub_le (cube l + cube m) (cube m)
      rw [norm_cube, norm_cube] at h1
      linarith
    · right
      have hlt : ‖l‖ < 2 * ‖m‖ := by
        by_contra h'
        replace h' := not_lt.mp h'
        apply hc
        have := pow_le_pow_left₀ (by positivity) h' 3
        nlinarith [pow_nonneg hM 3]
      have h := norm_mul_le_two_norm_formMul l m
      nlinarith
  have hmul := norm_hess_twoCube g
  have hd := norm_nonneg (det2 g)
  obtain ⟨l, m⟩ := g
  simp only at hmul
  rw [hmul, Prod.norm_def]
  rcases le_total ‖m‖ ‖l‖ with h | h
  · rw [max_eq_left h]
    rcases key l m h with h1 | h1
    · left; simpa [twoCube] using h1
    · right; nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖det2 (l, m)‖)]
  · rw [max_eq_right h]
    rcases key m l h with h1 | h1
    · left; simpa [twoCube, add_comm] using h1
    · right
      rw [formMul_comm] at h1
      nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖det2 (l, m)‖)]

end SLT.PositionFour
