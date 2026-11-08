/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT

/-!
# Zoo: the 1-2-2-1 MLP arrangement ideals at model level (brief 04, T5)

Source: resnet-bridge `mlp/` (scout `mlp-scout`, run 04, AI-reviewed; read only, not a dependency):
`s2prime_arrangement.md` (S2′, dead types), `s2pp_merged.md` (S2″, merged types),
`hunt_cancellation.md` (the `(dup, dup)` point). Each realization is reduced **on paper** (chart
lemma: an analytic left inverse eliminates the regular coordinates) to

  `(regular coordinates y) + J`,  `J` a monomial ideal in the remaining coordinates,

and `(λ, m)` is read off as `(n_reg/2 + λ_J, m_J)`. Here the **model level** is Lean-certified: the
loss `Σ yᵢ² + K_J`, with `K_J` the sum of squares of the generators of `J`, has the stated pair,
through the core's two-sided Newton theorem (`SLT.Newton.newton_box_units`) for the `J` part and
the disjoint-block rule (`SLT.HasLaplacePair.prod`, M1) for the regular part. The chart reductions
themselves stay on paper.

**S2′.** The spare ideal is **one function** of the five spare weights `(a, B, q, r, c)`:
`J = (aB, cq, car)`, `spareLoss = (aB)² + (cq)² + (car)²`. Each arrangement is a *point* of the
true set `{aB = cq = car = 0}`, with the weights the arrangement leaves alive as nonzero
parameters. So the Lean also certifies the localization step ("which edges must be cut"): at
`(out, in)` the loss is comparable to `B² + q² + r²`, at `(in, out)` to `a² + c²`.

| arrangement (L1, L2) | point `(a, B, q, r, c)` | `K_J ≍` | `J`-pair | total (`+ (3/2, 1)`) |
|---|---|---|---|---|
| (in, out) | `(0, B, q, r, 0)` | `a² + c²` | `(1, 1)` | `(5/2, 1)` |
| (out, in) | `(a, 0, 0, 0, c)` | `B² + q² + r²` | `(3/2, 1)` | `(3, 1)` |
| (in, both) | `(0, B, 0, 0, 0)` | `a² + c²q²` | `(1, 2)` | `(5/2, 2)` |
| (both, in) | `(0, 0, 0, 0, c)` | `a²B² + q² + a²r²` | `(1, 1)` | `(5/2, 1)` |
| (both, out) | `(0, 0, q, 0, 0)` | `a²B² + c²` | `(1, 2)` | `(5/2, 2)` |
| (out, both) | `(a, 0, 0, 0, 0)` | `B² + c²q² + c²r²` | `(1, 1)` | `(5/2, 1)` |

**S2″ and the hunt.** The residual ideals live in the source's own local coordinates:

| point | regular | residual | total |
|---|---|---|---|
| M1, M4 | 4 | `(ε²)` | `(9/4, 1)` |
| M2 | 4 | `(w, p)²` | `(5/2, 1)` |
| M3 (slice `ρ = 0`) | 4 | `(ε², ρε)` at `(0, 0)` | `(5/2, 2)` |
| M3′ (`ρ = ρ* ≠ 0`) | 4 | `(ε², ρε)` at `(0, ρ*)` | `(5/2, 1)` |
| hunt T4, (dup, dup) | 3 | `(g, ε)²` | `(2, 1)` |

M3 and M3′ are again one function at two points, as in the source (M3 is the special slice of
M3′'s component).

**Consumers:** `outIn_ne_inOut` (S2′'s headline dichotomy) and `m4_ne_m3'` (S2″'s).

All pairs are for the Lebesgue prior on a box around the point. The box half-width satisfies
`δ ≤ |x*|/2` for every coordinate `x*` that is nonzero at the point, and `δ ≤ 1` where the
comparison needs it.
-/

@[expose] public section

namespace SLT.Zoo.MLP

open MeasureTheory Set SLT SLT.Newton SLT.NC
open scoped ENNReal

variable {d : ℕ}

/-! ### Pure-power exponent sets -/

/-- The pure-power exponent set `{kᵢ eᵢ : i ∈ s}`: the monomial sum is `Σ_{i ∈ s} |yᵢ|^{kᵢ}`. -/
noncomputable def powΓ (s : Finset (Fin d)) (k : Fin d → ℝ) : Finset (Fin d → ℝ) :=
  s.image fun i => Pi.single i (k i)

/-- The exponents of a pure-power set are nonnegative. -/
theorem powΓ_nonneg {s : Finset (Fin d)} {k : Fin d → ℝ} (hk : ∀ i ∈ s, 0 < k i) :
    ∀ α ∈ powΓ s k, ∀ j, 0 ≤ α j := by
  intro α hα j
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hα
  by_cases h : j = i
  · subst h; simp [(hk j hi).le]
  · simp [h]

/-- `⟨kᵢ eᵢ, u⟩ = kᵢ uᵢ`. -/
theorem dot_single (i : Fin d) (a : ℝ) (u : Fin d → ℝ) :
    ∑ j, (Pi.single i a : Fin d → ℝ) j * u j = a * u i := by
  simp [Pi.single_apply, ite_mul]

/-- The optimal weight vector of a pure-power set: `uᵢ = T/kᵢ` on `s`, `0` off `s`. -/
noncomputable def powCert (s : Finset (Fin d)) (k : Fin d → ℝ) : Fin d → ℝ :=
  fun j => if j ∈ s then (∑ i ∈ s, (k i)⁻¹)⁻¹ * (k j)⁻¹ else 0

/-- `Σ_{i ∈ s} 1/kᵢ > 0`. -/
theorem powSum_pos {s : Finset (Fin d)} {k : Fin d → ℝ} (hs : s.Nonempty)
    (hk : ∀ i ∈ s, 0 < k i) : 0 < ∑ i ∈ s, (k i)⁻¹ :=
  Finset.sum_pos (fun i hi => inv_pos.mpr (hk i hi)) hs

/-- `powCert` certifies `t = (Σ_{i ∈ s} 1/kᵢ)⁻¹`. -/
theorem isNewtonCert_powCert {s : Finset (Fin d)} {k : Fin d → ℝ} (hs : s.Nonempty)
    (hk : ∀ i ∈ s, 0 < k i) :
    IsNewtonCert (powΓ s k) (∑ i ∈ s, (k i)⁻¹)⁻¹ (powCert s k) := by
  have hT := powSum_pos hs hk
  refine ⟨fun j => ?_, ?_, ?_⟩
  · unfold powCert; split_ifs with h
    · exact mul_nonneg (inv_nonneg.mpr hT.le) (inv_nonneg.mpr (hk j h).le)
    · exact le_rfl
  · unfold powCert
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum, inv_mul_cancel₀ hT.ne']
  · intro α hα
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hα
    rw [dot_single]
    simp only [powCert, hi, ite_true]
    have := (hk i hi).ne'
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ this, mul_one]

/-- Every certificate for `t` has `t / kᵢ ≤ uᵢ` on `s`. -/
theorem le_of_isNewtonCert {s : Finset (Fin d)} {k : Fin d → ℝ} (hk : ∀ i ∈ s, 0 < k i)
    {t : ℝ} {u : Fin d → ℝ} (h : IsNewtonCert (powΓ s k) t u) :
    ∀ i ∈ s, t * (k i)⁻¹ ≤ u i := by
  intro i hi
  have := h.2.2 _ (Finset.mem_image_of_mem _ hi)
  rw [dot_single] at this
  rw [mul_inv_le_iff₀ (hk i hi), mul_comm]; exact this

/-- `t*` of a pure-power set: `(Σ_{i ∈ s} 1/kᵢ)⁻¹`. -/
theorem newtonDist_powΓ {s : Finset (Fin d)} {k : Fin d → ℝ} (hs : s.Nonempty)
    (hk : ∀ i ∈ s, 0 < k i) : newtonDist (powΓ s k) = (∑ i ∈ s, (k i)⁻¹)⁻¹ := by
  have hT := powSum_pos hs hk
  refine newtonDist_eq (isNewtonCert_powCert hs hk) fun t u h => ?_
  have hle := le_of_isNewtonCert hk h
  have h1 : t * ∑ i ∈ s, (k i)⁻¹ ≤ 1 := by
    rw [Finset.mul_sum, ← h.2.1]
    exact (Finset.sum_le_sum hle).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => h.1 j)
  calc t = t * (∑ i ∈ s, (k i)⁻¹) * (∑ i ∈ s, (k i)⁻¹)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hT.ne', mul_one]
    _ ≤ 1 * (∑ i ∈ s, (k i)⁻¹)⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hT.le)
    _ = _ := one_mul _

/-- The optimal weights of a pure-power set are the single point `powCert`. -/
theorem optWeights_powΓ {s : Finset (Fin d)} {k : Fin d → ℝ} (hs : s.Nonempty)
    (hk : ∀ i ∈ s, 0 < k i) : optWeights (powΓ s k) = {powCert s k} := by
  have hT := powSum_pos hs hk
  ext u
  simp only [optWeights, mem_ofPred_eq, mem_singleton_iff, newtonDist_powΓ hs hk]
  constructor
  · intro h
    have hle := le_of_isNewtonCert hk h
    have hv : ∀ j, powCert s k j ≤ u j := fun j => by
      unfold powCert; split_ifs with hj
      · exact hle j hj
      · exact h.1 j
    have hsum : ∑ j, (u j - powCert s k j) = 0 := by
      rw [Finset.sum_sub_distrib, h.2.1, (isNewtonCert_powCert hs hk).2.1, sub_self]
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sub_nonneg.mpr (hv j)).mp hsum
    funext j; linarith [this j (Finset.mem_univ _)]
  · rintro rfl; exact isNewtonCert_powCert hs hk

/-- A single optimal weight vector gives multiplicity one. -/
theorem newtonMult_eq_one {Γ : Finset (Fin d → ℝ)} {p : Fin d → ℝ} (h : optWeights Γ = {p}) :
    newtonMult Γ = 1 := by
  rw [newtonMult, h, direction_affineSpan, vectorSpan_singleton, finrank_bot]

/-- The monomial sum of a pure-power set. -/
theorem monoSum_powΓ {s : Finset (Fin d)} {k : Fin d → ℝ} (hk : ∀ i ∈ s, 0 < k i)
    (y : Fin d → ℝ) : monoSum (powΓ s k) y = ∑ i ∈ s, |y i| ^ k i := by
  unfold monoSum powΓ
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl fun i _ => ?_
    unfold monomial
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  · intro i hi j _ hij
    by_contra hne
    have := congrFun hij i
    simp only at this
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
    exact (hk i hi).ne' this

/-- **Pure-power comparison ⇒ pair** `(Σ_{i ∈ s} 1/kᵢ, 1)`, through `newton_box_units`. -/
theorem pair_of_powΓ {s : Finset (Fin d)} {k : Fin d → ℝ} (hs : s.Nonempty)
    (hk : ∀ i ∈ s, 0 < k i) {δ : ℝ} (hδ : 0 < δ) {K : (Fin d → ℝ) → ℝ} (hK : Measurable K)
    {c C : ℝ} (hc : 0 < c) (hlo : ∀ y ∈ box δ, c * ∑ i ∈ s, |y i| ^ k i ≤ K y)
    (hhi : ∀ y ∈ box δ, K y ≤ C * ∑ i ∈ s, |y i| ^ k i) :
    HasLaplacePair (Z (volume.restrict (box δ)) K) (∑ i ∈ s, (k i)⁻¹) 1 := by
  have h := newton_box_units hδ (powΓ_nonneg hk)
    (by rw [newtonDist_powΓ hs hk]; exact inv_pos.mpr (powSum_pos hs hk)) hK
    (f := fun _ => 1) (a := 1) (b := 1) one_pos hc
    (fun y hy => by rw [monoSum_powΓ hk]; exact hlo y hy)
    (fun y hy => by rw [monoSum_powΓ hk]; exact hhi y hy) (fun y _ => by simp) (fun y _ => by simp)
  rw [show ((volume.restrict (box δ)).withDensity fun _ => (1 : ℝ≥0∞)) =
      volume.restrict (box δ) from withDensity_one, newtonDist_powΓ hs hk, inv_inv,
    newtonMult_eq_one (optWeights_powΓ hs hk)] at h
  exact h

/-! ### The regular factor and the disjoint-block rule -/

/-- The regular factor `Σ yᵢ²` in `n` regular coordinates. -/
def regLoss (n : ℕ) (y : Fin n → ℝ) : ℝ := ∑ i, y i ^ 2

/-- The regular factor is measurable. -/
theorem measurable_regLoss (n : ℕ) : Measurable (regLoss n) := by
  unfold regLoss; fun_prop

/-- **The regular factor has pair `(n/2, 1)`.** -/
theorem regLoss_pair {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    HasLaplacePair (Z (volume.restrict (box δ)) (regLoss n)) (n / 2) 1 := by
  have hs : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  have h := pair_of_powΓ (k := fun _ => 2) hs (fun _ _ => two_pos) hδ (measurable_regLoss n)
    (c := 1) (C := 1) one_pos
    (fun y _ => by simp only [regLoss, Real.rpow_two, sq_abs, one_mul]; exact le_rfl)
    (fun y _ => by simp only [regLoss, Real.rpow_two, sq_abs, one_mul]; exact le_rfl)
  simpa [div_eq_mul_inv] using h

/-- **Regular factor ⊕ residual** (`HasLaplacePair.prod`, M1): `(n/2 + λ, m)`. -/
theorem regular_add_pair {β : Type*} [MeasurableSpace β] {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ : 0 < δ) {ν : Measure β} [SFinite ν] {K : β → ℝ} (hK : Measurable K) {lam : ℝ} {m : ℕ}
    (H : HasLaplacePair (Z ν K) lam m) :
    HasLaplacePair (Z ((volume.restrict (box δ)).prod ν) (fun p => regLoss n p.1 + K p.2))
      (n / 2 + lam) m := by
  have h := (regLoss_pair hn hδ).prod (measurable_regLoss n) hK H
  rwa [show 1 + m - 1 = m by omega] at h

/-- **Moving the box to the origin** (as in `Zoo.ReadWrite.Z_translate`). -/
theorem Z_translate (p : Fin d → ℝ) (δ : ℝ) (K : (Fin d → ℝ) → ℝ) :
    Z (volume.restrict {θ | θ - p ∈ box δ}) K =
      Z (volume.restrict (box δ)) (fun y => K (p + y)) := by
  funext N
  simp only [Z]
  have e := (measurePreserving_add_left (volume : Measure (Fin d → ℝ)) p)
    |>.setLIntegral_comp_preimage_emb (MeasurableEquiv.addLeft p).measurableEmbedding
    (fun θ => ENNReal.ofReal (Real.exp (-(N * K θ)))) {θ | θ - p ∈ box δ}
  have hpre : (fun y => p + y) ⁻¹' {θ | θ - p ∈ box δ} = box δ := by
    ext y; simp
  rw [hpre] at e
  exact e.symm

/-- A coordinate of a box point is at most `δ` in absolute value. -/
theorem abs_le_of_mem_box {δ : ℝ} {y : Fin d → ℝ} (hy : y ∈ box δ) (i : Fin d) : |y i| ≤ δ :=
  abs_le.mpr (hy i (mem_univ _))

/-- **Units**: on the box, `x* + yᵢ` stays between `|x*|/2` and `3|x*|/2`, squared. -/
theorem unit_sq_bounds {x δ t : ℝ} (hδx : δ ≤ |x| / 2) (ht : |t| ≤ δ) :
    x ^ 2 / 4 ≤ (x + t) ^ 2 ∧ (x + t) ^ 2 ≤ 9 * x ^ 2 / 4 := by
  have h1 : |x| / 2 ≤ |x + t| := by
    have := abs_add_le (x + t) (-t)
    rw [add_neg_cancel_right, abs_neg] at this; linarith
  have h2 : |x + t| ≤ 3 * |x| / 2 := by
    have := abs_add_le x t; linarith
  have h0 : 0 ≤ |x| / 2 := by positivity
  constructor
  · rw [← sq_abs (x + t), ← sq_abs x]; nlinarith
  · rw [← sq_abs (x + t), ← sq_abs x]; nlinarith [abs_nonneg (x + t)]

/-- On a box with `δ ≤ 1`, `yᵢ² ≤ 1`. -/
theorem sq_le_one_of_mem_box {δ : ℝ} (hδ1 : δ ≤ 1) {y : Fin d → ℝ} (hy : y ∈ box δ) (i : Fin d) :
    y i ^ 2 ≤ 1 := by
  have := abs_le_of_mem_box hy i
  rw [← sq_abs]; nlinarith [abs_nonneg (y i)]

/-- The pure-power sum with all exponents `2` is a sum of squares. -/
theorem sum_abs_rpow_two (s : Finset (Fin d)) (y : Fin d → ℝ) :
    ∑ i ∈ s, |y i| ^ ((fun _ => (2 : ℝ)) i) = ∑ i ∈ s, y i ^ 2 := by
  simp only [Real.rpow_two, sq_abs]

/-- `(x + t)² ≤ 2x² + 2` when `|t| ≤ 1`. -/
theorem add_sq_le {x t : ℝ} (ht : t ^ 2 ≤ 1) : (x + t) ^ 2 ≤ 2 * x ^ 2 + 2 := by
  nlinarith [sq_nonneg (x - t)]

/-! ### S2′: the spare ideal `J = (aB, cq, car)` -/

/-- The spare loss `(aB)² + (cq)² + (car)²` in the coordinates `(a, B, q, r, c) = z 0, …, z 4`. -/
def spareLoss (z : Fin 5 → ℝ) : ℝ := (z 0 * z 1) ^ 2 + (z 4 * z 2) ^ 2 + (z 4 * z 3 * z 0) ^ 2

/-- The spare loss is measurable. -/
theorem measurable_spareLoss : Measurable spareLoss := by
  unfold spareLoss; fun_prop

/-- The spare loss near a point `(a, B, q, r, c)`, expanded. -/
theorem spareLoss_add (a B q r c : ℝ) (y : Fin 5 → ℝ) :
    spareLoss (![a, B, q, r, c] + y) = (a + y 0) ^ 2 * (B + y 1) ^ 2 +
      (c + y 4) ^ 2 * (q + y 2) ^ 2 + (c + y 4) ^ 2 * (r + y 3) ^ 2 * (a + y 0) ^ 2 := by
  simp only [spareLoss, Pi.add_apply]
  simp
  ring

/-- The S2′ model: three regular (narrow-chain) coordinates plus the spare loss. -/
def s2pLoss (p : (Fin 3 → ℝ) × (Fin 5 → ℝ)) : ℝ := regLoss 3 p.1 + spareLoss p.2

/-- The prior of the S2′ model: a box of half-width `δ` around `0` in the regular coordinates and
around the point `pt` in the spare coordinates. -/
noncomputable def s2pPrior (pt : Fin 5 → ℝ) (δ : ℝ) : Measure ((Fin 3 → ℝ) × (Fin 5 → ℝ)) :=
  (volume.restrict (box δ)).prod (volume.restrict {z | z - pt ∈ box δ})

/-- An S2′ spare pair `(λ, m)` gives the total pair `(3/2 + λ, m)`. -/
theorem s2p_pair_of_spare {pt : Fin 5 → ℝ} {δ : ℝ} (hδ : 0 < δ) {lam : ℝ} {m : ℕ}
    (H : HasLaplacePair (Z (volume.restrict {z | z - pt ∈ box δ}) spareLoss) lam m) :
    HasLaplacePair (Z (s2pPrior pt δ) s2pLoss) (3 / 2 + lam) m := by
  have := regular_add_pair (n := 3) (by norm_num) hδ measurable_spareLoss H
  exact_mod_cast this

/-- **(in, out)**: `a = c = 0`, with `B, q ≠ 0` and `r` arbitrary. `K_J ≍ a² + c²`, pair
`(1, 1)`. -/
theorem spare_inOut_pair {B q r δ : ℝ} (hB : B ≠ 0) (hq : q ≠ 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδB : δ ≤ |B| / 2) (hδq : δ ≤ |q| / 2) :
    HasLaplacePair (Z (volume.restrict {z | z - ![0, B, q, r, 0] ∈ box δ}) spareLoss) 1 1 := by
  rw [Z_translate]
  have h := pair_of_powΓ (s := {0, 4}) (k := fun _ => 2) (by simp) (fun _ _ => two_pos) hδ
    (K := fun y => spareLoss (![0, B, q, r, 0] + y))
    (measurable_spareLoss.comp (measurable_const_add _))
    (c := min (B ^ 2 / 4) (q ^ 2 / 4)) (C := 9 * B ^ 2 / 4 + 9 * q ^ 2 / 4 + 2 * r ^ 2 + 2)
    (lt_min (by positivity) (by positivity)) ?_ ?_
  · convert h using 1; rw [Finset.sum_pair (by decide)]; norm_num
  all_goals intro y hy
  all_goals rw [sum_abs_rpow_two, Finset.sum_pair (by decide), spareLoss_add]
  all_goals simp only [zero_add]
  all_goals have hB' := unit_sq_bounds hδB (abs_le_of_mem_box hy 1)
  all_goals have hq' := unit_sq_bounds hδq (abs_le_of_mem_box hy 2)
  all_goals have hr' := add_sq_le (x := r) (sq_le_one_of_mem_box hδ1 hy 3)
  all_goals have h0 := sq_le_one_of_mem_box hδ1 hy 0
  · have e1 := mul_le_mul_of_nonneg_left ((min_le_left _ (q ^ 2 / 4)).trans hB'.1) (sq_nonneg (y 0))
    have e2 := mul_le_mul_of_nonneg_left ((min_le_right (B ^ 2 / 4) _).trans hq'.1)
      (sq_nonneg (y 4))
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (y 4)) (sq_nonneg (r + y 3))) (sq_nonneg (y 0))]
  · have e1 := mul_le_mul_of_nonneg_left hB'.2 (sq_nonneg (y 0))
    have e2 := mul_le_mul_of_nonneg_left hq'.2 (sq_nonneg (y 4))
    have e3 : (r + y 3) ^ 2 * y 0 ^ 2 ≤ (2 * r ^ 2 + 2) * 1 :=
      mul_le_mul hr' h0 (sq_nonneg _) (by positivity)
    have e4 := mul_le_mul_of_nonneg_left e3 (sq_nonneg (y 4))
    nlinarith [sq_nonneg (y 0), sq_nonneg (y 4), sq_nonneg B, sq_nonneg q, sq_nonneg r]

/-- **(out, in)**: `B = q = r = 0`, with `a, c ≠ 0`. Now `car = unit · r`, so `r` must be cut too:
`K_J ≍ B² + q² + r²`, pair `(3/2, 1)`. -/
theorem spare_outIn_pair {a c δ : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) (hδ : 0 < δ)
    (hδa : δ ≤ |a| / 2) (hδc : δ ≤ |c| / 2) :
    HasLaplacePair (Z (volume.restrict {z | z - ![a, 0, 0, 0, c] ∈ box δ}) spareLoss)
      (3 / 2) 1 := by
  rw [Z_translate]
  have hca : 0 < c ^ 2 / 4 * (a ^ 2 / 4) := by positivity
  have h := pair_of_powΓ (s := {1, 2, 3}) (k := fun _ => 2) (by simp) (fun _ _ => two_pos) hδ
    (K := fun y => spareLoss (![a, 0, 0, 0, c] + y))
    (measurable_spareLoss.comp (measurable_const_add _))
    (c := min (a ^ 2 / 4) (min (c ^ 2 / 4) (c ^ 2 / 4 * (a ^ 2 / 4))))
    (C := 9 * a ^ 2 / 4 + 9 * c ^ 2 / 4 + 9 * c ^ 2 / 4 * (9 * a ^ 2 / 4))
    (lt_min (by positivity) (lt_min (by positivity) hca)) ?_ ?_
  · convert h using 1; simp; norm_num
  all_goals intro y hy
  all_goals rw [sum_abs_rpow_two, Finset.sum_insert (by decide), Finset.sum_pair (by decide),
    spareLoss_add]
  all_goals simp only [zero_add]
  all_goals have ha' := unit_sq_bounds hδa (abs_le_of_mem_box hy 0)
  all_goals have hc' := unit_sq_bounds hδc (abs_le_of_mem_box hy 4)
  · set m := min (a ^ 2 / 4) (min (c ^ 2 / 4) (c ^ 2 / 4 * (a ^ 2 / 4)))
    have m1 : m ≤ a ^ 2 / 4 := min_le_left _ _
    have m2 : m ≤ c ^ 2 / 4 := (min_le_right _ _).trans (min_le_left _ _)
    have m3 : m ≤ c ^ 2 / 4 * (a ^ 2 / 4) := (min_le_right _ _).trans (min_le_right _ _)
    have e1 := mul_le_mul_of_nonneg_left (m1.trans ha'.1) (sq_nonneg (y 1))
    have e2 := mul_le_mul_of_nonneg_left (m2.trans hc'.1) (sq_nonneg (y 2))
    have e3 : m ≤ (c + y 4) ^ 2 * (a + y 0) ^ 2 :=
      m3.trans (mul_le_mul hc'.1 ha'.1 (by positivity) (sq_nonneg _))
    have e4 := mul_le_mul_of_nonneg_left e3 (sq_nonneg (y 3))
    nlinarith
  · have e1 := mul_le_mul_of_nonneg_left ha'.2 (sq_nonneg (y 1))
    have e2 := mul_le_mul_of_nonneg_left hc'.2 (sq_nonneg (y 2))
    have e3 : (c + y 4) ^ 2 * (a + y 0) ^ 2 ≤ 9 * c ^ 2 / 4 * (9 * a ^ 2 / 4) :=
      mul_le_mul hc'.2 ha'.2 (sq_nonneg _) (by positivity)
    have e4 := mul_le_mul_of_nonneg_left e3 (sq_nonneg (y 3))
    nlinarith

/-! ### Explicit Newton data for the non-diagonal spare ideals -/

/-- A segment of optimal weights gives multiplicity two. -/
theorem newtonMult_eq_two {Γ : Finset (Fin d → ℝ)} {p q : Fin d → ℝ}
    (h : optWeights Γ = segment ℝ p q) (hpq : p ≠ q) : newtonMult Γ = 2 := by
  rw [newtonMult, h, ← convexHull_pair, affineSpan_convexHull, direction_affineSpan,
    vectorSpan_pair, finrank_span_singleton]
  exact vsub_ne_zero.mpr hpq

/-- **General exponent set ⇒ pair**, through `newton_box_units` with the Lebesgue prior. -/
theorem pair_of_Γ {Γ : Finset (Fin d → ℝ)} (hΓ : ∀ α ∈ Γ, ∀ i, 0 ≤ α i)
    (hd : 0 < newtonDist Γ) {δ : ℝ} (hδ : 0 < δ) {K : (Fin d → ℝ) → ℝ} (hK : Measurable K)
    {c C : ℝ} (hc : 0 < c) (hlo : ∀ y ∈ box δ, c * monoSum Γ y ≤ K y)
    (hhi : ∀ y ∈ box δ, K y ≤ C * monoSum Γ y) :
    HasLaplacePair (Z (volume.restrict (box δ)) K) (newtonDist Γ)⁻¹ (newtonMult Γ) := by
  have h := newton_box_units hδ hΓ hd hK (f := fun _ => 1) (a := 1) (b := 1) one_pos hc hlo hhi
    (fun y _ => by simp) (fun y _ => by simp)
  rwa [show ((volume.restrict (box δ)).withDensity fun _ => (1 : ℝ≥0∞)) =
      volume.restrict (box δ) from withDensity_one] at h

/-- A monomial in five variables, written out. -/
theorem monomial_five (α y : Fin 5 → ℝ) :
    monomial α y = |y 0| ^ α 0 * |y 1| ^ α 1 * |y 2| ^ α 2 * |y 3| ^ α 3 * |y 4| ^ α 4 := by
  simp [monomial, Fin.prod_univ_five]

/-- `(in, both)`: `Γ = {2e_a, 2e_q + 2e_c}`. -/
noncomputable def ΓinBoth : Finset (Fin 5 → ℝ) := {![2, 0, 0, 0, 0], ![0, 0, 2, 0, 2]}
/-- `(both, in)`: `Γ = {2e_a + 2e_B, 2e_q, 2e_a + 2e_r}`. -/
noncomputable def ΓbothIn : Finset (Fin 5 → ℝ) :=
  {![2, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![2, 0, 0, 2, 0]}
/-- `(both, out)`: `Γ = {2e_a + 2e_B, 2e_c}`. -/
noncomputable def ΓbothOut : Finset (Fin 5 → ℝ) := {![2, 2, 0, 0, 0], ![0, 0, 0, 0, 2]}
/-- `(out, both)`: `Γ = {2e_B, 2e_q + 2e_c, 2e_r + 2e_c}`. -/
noncomputable def ΓoutBoth : Finset (Fin 5 → ℝ) :=
  {![0, 2, 0, 0, 0], ![0, 0, 2, 0, 2], ![0, 0, 0, 2, 2]}

/-- The exponents of `ΓinBoth` are nonnegative. -/
theorem ΓinBoth_nonneg : ∀ α ∈ ΓinBoth, ∀ i, 0 ≤ α i := by
  intro α hα i; simp only [ΓinBoth, Finset.mem_insert, Finset.mem_singleton] at hα
  rcases hα with rfl | rfl <;> fin_cases i <;> norm_num
/-- The exponents of `ΓbothIn` are nonnegative. -/
theorem ΓbothIn_nonneg : ∀ α ∈ ΓbothIn, ∀ i, 0 ≤ α i := by
  intro α hα i; simp only [ΓbothIn, Finset.mem_insert, Finset.mem_singleton] at hα
  rcases hα with rfl | rfl | rfl <;> fin_cases i <;> norm_num
/-- The exponents of `ΓbothOut` are nonnegative. -/
theorem ΓbothOut_nonneg : ∀ α ∈ ΓbothOut, ∀ i, 0 ≤ α i := by
  intro α hα i; simp only [ΓbothOut, Finset.mem_insert, Finset.mem_singleton] at hα
  rcases hα with rfl | rfl <;> fin_cases i <;> norm_num
/-- The exponents of `ΓoutBoth` are nonnegative. -/
theorem ΓoutBoth_nonneg : ∀ α ∈ ΓoutBoth, ∀ i, 0 ≤ α i := by
  intro α hα i; simp only [ΓoutBoth, Finset.mem_insert, Finset.mem_singleton] at hα
  rcases hα with rfl | rfl | rfl <;> fin_cases i <;> norm_num

/-- (in, both): `t* = 1`. -/
theorem newtonDist_inBoth : newtonDist ΓinBoth = 1 := by
  refine newtonDist_eq (u := ![1 / 2, 0, 1 / 2, 0, 0]) ⟨fun i => by fin_cases i <;> norm_num,
    by simp [Fin.sum_univ_five]; norm_num, ?_⟩ ?_
  · intro α hα; simp only [ΓinBoth, Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> simp [Fin.sum_univ_five]
  · rintro t u ⟨h0, h1, h2⟩
    have a1 := h2 ![2, 0, 0, 0, 0] (by simp [ΓinBoth])
    have a2 := h2 ![0, 0, 2, 0, 2] (by simp [ΓinBoth])
    simp [Fin.sum_univ_five] at h1 a1 a2
    linarith [h0 1, h0 3]

/-- (in, both): `O` is a segment. -/
theorem optWeights_inBoth : optWeights ΓinBoth =
    segment ℝ ![1 / 2, 0, 1 / 2, 0, 0] ![1 / 2, 0, 0, 0, 1 / 2] := by
  ext u
  rw [optWeights, newtonDist_inBoth]
  simp only [IsNewtonCert, ΓinBoth, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq, Fin.sum_univ_five, mem_ofPred_eq]
  constructor
  · rintro ⟨h0, h1, a1, a2⟩
    norm_num at a1 a2
    have := h0 0; have := h0 1; have := h0 2; have := h0 3; have := h0 4
    refine ⟨2 * u 2, 2 * u 4, by linarith, by linarith, by linarith, ?_⟩
    funext i; fin_cases i <;> simp <;> linarith
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨fun i => by fin_cases i <;> simp [ha, hb, add_nonneg], by simp; linarith,
      by simp; nlinarith, by simp; nlinarith⟩

/-- (in, both): `m = 2`. -/
theorem newtonMult_inBoth : newtonMult ΓinBoth = 2 :=
  newtonMult_eq_two optWeights_inBoth (fun h => by have := congrFun h 2; norm_num at this)

/-- (both, in): `t* = 1`. -/
theorem newtonDist_bothIn : newtonDist ΓbothIn = 1 := by
  refine newtonDist_eq (u := ![1 / 2, 0, 1 / 2, 0, 0]) ⟨fun i => by fin_cases i <;> norm_num,
    by simp [Fin.sum_univ_five]; norm_num, ?_⟩ ?_
  · intro α hα; simp only [ΓbothIn, Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl | rfl <;> simp [Fin.sum_univ_five]
  · rintro t u ⟨h0, h1, h2⟩
    have a1 := h2 ![2, 2, 0, 0, 0] (by simp [ΓbothIn])
    have a2 := h2 ![0, 0, 2, 0, 0] (by simp [ΓbothIn])
    simp [Fin.sum_univ_five] at h1 a1 a2
    linarith [h0 3, h0 4]

/-- (both, in): `O` is a single point. -/
theorem optWeights_bothIn : optWeights ΓbothIn = {![1 / 2, 0, 1 / 2, 0, 0]} := by
  ext u
  rw [optWeights, newtonDist_bothIn]
  simp only [IsNewtonCert, ΓbothIn, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq, Fin.sum_univ_five, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨h0, h1, a1, a2, a3⟩
    norm_num at a1 a2 a3
    have := h0 0; have := h0 1; have := h0 2; have := h0 3; have := h0 4
    funext i; fin_cases i <;> simp <;> linarith
  · rintro rfl
    refine ⟨fun i => by fin_cases i <;> norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num⟩

/-- (both, out): `t* = 1`. -/
theorem newtonDist_bothOut : newtonDist ΓbothOut = 1 := by
  refine newtonDist_eq (u := ![1 / 2, 0, 0, 0, 1 / 2]) ⟨fun i => by fin_cases i <;> norm_num,
    by simp [Fin.sum_univ_five]; norm_num, ?_⟩ ?_
  · intro α hα; simp only [ΓbothOut, Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> simp [Fin.sum_univ_five]
  · rintro t u ⟨h0, h1, h2⟩
    have a1 := h2 ![2, 2, 0, 0, 0] (by simp [ΓbothOut])
    have a2 := h2 ![0, 0, 0, 0, 2] (by simp [ΓbothOut])
    simp [Fin.sum_univ_five] at h1 a1 a2
    linarith [h0 2, h0 3]

/-- (both, out): `O` is a segment. -/
theorem optWeights_bothOut : optWeights ΓbothOut =
    segment ℝ ![1 / 2, 0, 0, 0, 1 / 2] ![0, 1 / 2, 0, 0, 1 / 2] := by
  ext u
  rw [optWeights, newtonDist_bothOut]
  simp only [IsNewtonCert, ΓbothOut, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq, Fin.sum_univ_five, mem_ofPred_eq]
  constructor
  · rintro ⟨h0, h1, a1, a2⟩
    norm_num at a1 a2
    have := h0 0; have := h0 1; have := h0 2; have := h0 3; have := h0 4
    refine ⟨2 * u 0, 2 * u 1, by linarith, by linarith, by linarith, ?_⟩
    funext i; fin_cases i <;> simp <;> linarith
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨fun i => by fin_cases i <;> simp [ha, hb, add_nonneg], by simp; linarith,
      by simp; nlinarith, by simp; linarith⟩

/-- (both, out): `m = 2`. -/
theorem newtonMult_bothOut : newtonMult ΓbothOut = 2 :=
  newtonMult_eq_two optWeights_bothOut (fun h => by have := congrFun h 0; norm_num at this)

/-- (out, both): `t* = 1`. -/
theorem newtonDist_outBoth : newtonDist ΓoutBoth = 1 := by
  refine newtonDist_eq (u := ![0, 1 / 2, 0, 0, 1 / 2]) ⟨fun i => by fin_cases i <;> norm_num,
    by simp [Fin.sum_univ_five]; norm_num, ?_⟩ ?_
  · intro α hα; simp only [ΓoutBoth, Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl | rfl <;> simp [Fin.sum_univ_five]
  · rintro t u ⟨h0, h1, h2⟩
    have a1 := h2 ![0, 2, 0, 0, 0] (by simp [ΓoutBoth])
    have a2 := h2 ![0, 0, 2, 0, 2] (by simp [ΓoutBoth])
    simp [Fin.sum_univ_five] at h1 a1 a2
    linarith [h0 0, h0 3]

/-- (out, both): `O` is a single point. -/
theorem optWeights_outBoth : optWeights ΓoutBoth = {![0, 1 / 2, 0, 0, 1 / 2]} := by
  ext u
  rw [optWeights, newtonDist_outBoth]
  simp only [IsNewtonCert, ΓoutBoth, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq, Fin.sum_univ_five, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨h0, h1, a1, a2, a3⟩
    norm_num at a1 a2 a3
    have := h0 0; have := h0 1; have := h0 2; have := h0 3; have := h0 4
    funext i; fin_cases i <;> simp <;> linarith
  · rintro rfl
    refine ⟨fun i => by fin_cases i <;> norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num⟩

/-! ### The monomial sums -/

/-- (in, both): the monomial sum `a² + q²c²`. -/
theorem monoSum_inBoth (y : Fin 5 → ℝ) : monoSum ΓinBoth y = y 0 ^ 2 + y 2 ^ 2 * y 4 ^ 2 := by
  rw [monoSum, ΓinBoth, Finset.sum_pair (fun h => absurd (congrFun h 0) (by norm_num))]
  simp [monomial_five]

/-- (both, in): the monomial sum `a²B² + q² + a²r²`. -/
theorem monoSum_bothIn (y : Fin 5 → ℝ) :
    monoSum ΓbothIn y = y 0 ^ 2 * y 1 ^ 2 + (y 2 ^ 2 + y 0 ^ 2 * y 3 ^ 2) := by
  rw [monoSum, ΓbothIn, Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => absurd (congrFun h 0) (by norm_num),
        fun h => absurd (congrFun h 1) (by norm_num)⟩),
    Finset.sum_pair (fun h => absurd (congrFun h 0) (by norm_num))]
  simp [monomial_five]

/-- (both, out): the monomial sum `a²B² + c²`. -/
theorem monoSum_bothOut (y : Fin 5 → ℝ) : monoSum ΓbothOut y = y 0 ^ 2 * y 1 ^ 2 + y 4 ^ 2 := by
  rw [monoSum, ΓbothOut, Finset.sum_pair (fun h => absurd (congrFun h 0) (by norm_num))]
  simp [monomial_five]

/-- (out, both): the monomial sum `B² + q²c² + r²c²`. -/
theorem monoSum_outBoth (y : Fin 5 → ℝ) :
    monoSum ΓoutBoth y = y 1 ^ 2 + (y 2 ^ 2 * y 4 ^ 2 + y 3 ^ 2 * y 4 ^ 2) := by
  rw [monoSum, ΓoutBoth, Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => absurd (congrFun h 1) (by norm_num),
        fun h => absurd (congrFun h 1) (by norm_num)⟩),
    Finset.sum_pair (fun h => absurd (congrFun h 2) (by norm_num))]
  simp [monomial_five]

/-! ### The four non-diagonal spare points -/

/-- `y₃² y₄² ≤ 1`-type bound for two box coordinates. -/
theorem sq_mul_sq_le_one {δ : ℝ} (hδ1 : δ ≤ 1) {y : Fin d → ℝ} (hy : y ∈ box δ) (i j : Fin d) :
    y i ^ 2 * y j ^ 2 ≤ 1 := by
  have := sq_le_one_of_mem_box hδ1 hy i
  have := sq_le_one_of_mem_box hδ1 hy j
  nlinarith [sq_nonneg (y i), sq_nonneg (y j)]

/-- **(in, both)**: `a = q = r = c = 0`, with `B ≠ 0`. `K_J ≍ a² + c²q²`, pair `(1, 2)`. -/
theorem spare_inBoth_pair {B δ : ℝ} (hB : B ≠ 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδB : δ ≤ |B| / 2) :
    HasLaplacePair (Z (volume.restrict {z | z - ![0, B, 0, 0, 0] ∈ box δ}) spareLoss) 1 2 := by
  rw [Z_translate]
  have h := pair_of_Γ ΓinBoth_nonneg (by rw [newtonDist_inBoth]; norm_num) hδ
    (K := fun y => spareLoss (![0, B, 0, 0, 0] + y))
    (measurable_spareLoss.comp (measurable_const_add _))
    (c := min (B ^ 2 / 4) 1) (C := 9 * B ^ 2 / 4 + 2) (lt_min (by positivity) one_pos) ?_ ?_
  · rwa [newtonDist_inBoth, newtonMult_inBoth, inv_one] at h
  all_goals intro y hy
  all_goals rw [monoSum_inBoth, spareLoss_add]
  all_goals simp only [zero_add]
  all_goals have hB' := unit_sq_bounds hδB (abs_le_of_mem_box hy 1)
  · have e1 := mul_le_mul_of_nonneg_left ((min_le_left _ (1 : ℝ)).trans hB'.1) (sq_nonneg (y 0))
    have e2 := mul_le_mul_of_nonneg_right (min_le_right (B ^ 2 / 4) (1 : ℝ))
      (mul_nonneg (sq_nonneg (y 2)) (sq_nonneg (y 4)))
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (y 4)) (sq_nonneg (y 3))) (sq_nonneg (y 0))]
  · have e1 := mul_le_mul_of_nonneg_left hB'.2 (sq_nonneg (y 0))
    have e2 := mul_le_mul_of_nonneg_right (sq_mul_sq_le_one hδ1 hy 4 3) (sq_nonneg (y 0))
    nlinarith [sq_nonneg (y 0), mul_nonneg (sq_nonneg (y 2)) (sq_nonneg (y 4))]

/-- **(both, in)**: `a = B = q = r = 0`, with `c ≠ 0`. `K_J ≍ a²B² + q² + a²r²`, pair `(1, 1)`. -/
theorem spare_bothIn_pair {c δ : ℝ} (hc : c ≠ 0) (hδ : 0 < δ) (hδc : δ ≤ |c| / 2) :
    HasLaplacePair (Z (volume.restrict {z | z - ![0, 0, 0, 0, c] ∈ box δ}) spareLoss) 1 1 := by
  rw [Z_translate]
  have h := pair_of_Γ ΓbothIn_nonneg (by rw [newtonDist_bothIn]; norm_num) hδ
    (K := fun y => spareLoss (![0, 0, 0, 0, c] + y))
    (measurable_spareLoss.comp (measurable_const_add _))
    (c := min 1 (c ^ 2 / 4)) (C := 1 + 9 * c ^ 2 / 4) (lt_min one_pos (by positivity)) ?_ ?_
  · rwa [newtonDist_bothIn, newtonMult_eq_one optWeights_bothIn, inv_one] at h
  all_goals intro y hy
  all_goals rw [monoSum_bothIn, spareLoss_add]
  all_goals simp only [zero_add]
  all_goals have hc' := unit_sq_bounds hδc (abs_le_of_mem_box hy 4)
  · have m1 := min_le_left (1 : ℝ) (c ^ 2 / 4)
    have m2 := (min_le_right (1 : ℝ) (c ^ 2 / 4)).trans hc'.1
    have e1 := mul_le_mul_of_nonneg_right m1 (mul_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1)))
    have e2 := mul_le_mul_of_nonneg_right m2 (sq_nonneg (y 2))
    have e3 := mul_le_mul_of_nonneg_right m2 (mul_nonneg (sq_nonneg (y 3)) (sq_nonneg (y 0)))
    nlinarith
  · have e2 := mul_le_mul_of_nonneg_right hc'.2 (sq_nonneg (y 2))
    have e3 := mul_le_mul_of_nonneg_right hc'.2 (mul_nonneg (sq_nonneg (y 3)) (sq_nonneg (y 0)))
    nlinarith [mul_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1)), sq_nonneg (y 2),
      mul_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 3)), sq_nonneg c]

/-- **(both, out)**: `a = B = r = c = 0`, with `q ≠ 0`. `K_J ≍ a²B² + c²`, pair `(1, 2)`. -/
theorem spare_bothOut_pair {q δ : ℝ} (hq : q ≠ 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδq : δ ≤ |q| / 2) :
    HasLaplacePair (Z (volume.restrict {z | z - ![0, 0, q, 0, 0] ∈ box δ}) spareLoss) 1 2 := by
  rw [Z_translate]
  have h := pair_of_Γ ΓbothOut_nonneg (by rw [newtonDist_bothOut]; norm_num) hδ
    (K := fun y => spareLoss (![0, 0, q, 0, 0] + y))
    (measurable_spareLoss.comp (measurable_const_add _))
    (c := min 1 (q ^ 2 / 4)) (C := 2 + 9 * q ^ 2 / 4) (lt_min one_pos (by positivity)) ?_ ?_
  · rwa [newtonDist_bothOut, newtonMult_bothOut, inv_one] at h
  all_goals intro y hy
  all_goals rw [monoSum_bothOut, spareLoss_add]
  all_goals simp only [zero_add]
  all_goals have hq' := unit_sq_bounds hδq (abs_le_of_mem_box hy 2)
  · have m1 := min_le_left (1 : ℝ) (q ^ 2 / 4)
    have m2 := (min_le_right (1 : ℝ) (q ^ 2 / 4)).trans hq'.1
    have e1 := mul_le_mul_of_nonneg_right m1 (mul_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1)))
    have e2 := mul_le_mul_of_nonneg_left m2 (sq_nonneg (y 4))
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (y 4)) (sq_nonneg (y 3))) (sq_nonneg (y 0))]
  · have e2 := mul_le_mul_of_nonneg_left hq'.2 (sq_nonneg (y 4))
    have e3 := mul_le_mul_of_nonneg_left (sq_mul_sq_le_one hδ1 hy 3 0) (sq_nonneg (y 4))
    nlinarith [mul_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1)), sq_nonneg (y 4), sq_nonneg q]

/-- **(out, both)**: `B = q = r = c = 0`, with `a ≠ 0`. `K_J ≍ B² + c²q² + c²r²`, pair `(1, 1)`. -/
theorem spare_outBoth_pair {a δ : ℝ} (ha : a ≠ 0) (hδ : 0 < δ) (hδa : δ ≤ |a| / 2) :
    HasLaplacePair (Z (volume.restrict {z | z - ![a, 0, 0, 0, 0] ∈ box δ}) spareLoss) 1 1 := by
  rw [Z_translate]
  have h := pair_of_Γ ΓoutBoth_nonneg (by rw [newtonDist_outBoth]; norm_num) hδ
    (K := fun y => spareLoss (![a, 0, 0, 0, 0] + y))
    (measurable_spareLoss.comp (measurable_const_add _))
    (c := min (a ^ 2 / 4) 1) (C := 9 * a ^ 2 / 4 + 1) (lt_min (by positivity) one_pos) ?_ ?_
  · rwa [newtonDist_outBoth, newtonMult_eq_one optWeights_outBoth, inv_one] at h
  all_goals intro y hy
  all_goals rw [monoSum_outBoth, spareLoss_add]
  all_goals simp only [zero_add]
  all_goals have ha' := unit_sq_bounds hδa (abs_le_of_mem_box hy 0)
  · have m1 := (min_le_left (a ^ 2 / 4) (1 : ℝ)).trans ha'.1
    have m2 := min_le_right (a ^ 2 / 4) (1 : ℝ)
    have m3 := (min_le_left (a ^ 2 / 4) (1 : ℝ)).trans ha'.1
    have e1 := mul_le_mul_of_nonneg_right m1 (sq_nonneg (y 1))
    have e2 := mul_le_mul_of_nonneg_right m2 (mul_nonneg (sq_nonneg (y 2)) (sq_nonneg (y 4)))
    have e3 := mul_le_mul_of_nonneg_right m3 (mul_nonneg (sq_nonneg (y 3)) (sq_nonneg (y 4)))
    nlinarith
  · have e1 := mul_le_mul_of_nonneg_right ha'.2 (sq_nonneg (y 1))
    have e3 := mul_le_mul_of_nonneg_right ha'.2 (mul_nonneg (sq_nonneg (y 3)) (sq_nonneg (y 4)))
    nlinarith [sq_nonneg (y 1), mul_nonneg (sq_nonneg (y 2)) (sq_nonneg (y 4)),
      mul_nonneg (sq_nonneg (y 3)) (sq_nonneg (y 4)), sq_nonneg a]

/-! ### S2′ totals: regular `(3/2, 1)` ⊕ spare -/

section S2prime

variable {a B q r c δ : ℝ}

/-- **(in, out) total: `(5/2, 1)`.** -/
theorem s2p_inOut (hB : B ≠ 0) (hq : q ≠ 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδB : δ ≤ |B| / 2)
    (hδq : δ ≤ |q| / 2) : HasLaplacePair (Z (s2pPrior ![0, B, q, r, 0] δ) s2pLoss) (5 / 2) 1 := by
  convert s2p_pair_of_spare hδ (spare_inOut_pair (r := r) hB hq hδ hδ1 hδB hδq) using 1; norm_num

/-- **(out, in) total: `(3, 1)`.** -/
theorem s2p_outIn (ha : a ≠ 0) (hc : c ≠ 0) (hδ : 0 < δ) (hδa : δ ≤ |a| / 2)
    (hδc : δ ≤ |c| / 2) : HasLaplacePair (Z (s2pPrior ![a, 0, 0, 0, c] δ) s2pLoss) 3 1 := by
  convert s2p_pair_of_spare hδ (spare_outIn_pair ha hc hδ hδa hδc) using 1; norm_num

/-- **(in, both) total: `(5/2, 2)`.** -/
theorem s2p_inBoth (hB : B ≠ 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδB : δ ≤ |B| / 2) :
    HasLaplacePair (Z (s2pPrior ![0, B, 0, 0, 0] δ) s2pLoss) (5 / 2) 2 := by
  convert s2p_pair_of_spare hδ (spare_inBoth_pair hB hδ hδ1 hδB) using 1; norm_num

/-- **(both, in) total: `(5/2, 1)`.** -/
theorem s2p_bothIn (hc : c ≠ 0) (hδ : 0 < δ) (hδc : δ ≤ |c| / 2) :
    HasLaplacePair (Z (s2pPrior ![0, 0, 0, 0, c] δ) s2pLoss) (5 / 2) 1 := by
  convert s2p_pair_of_spare hδ (spare_bothIn_pair hc hδ hδc) using 1; norm_num

/-- **(both, out) total: `(5/2, 2)`.** -/
theorem s2p_bothOut (hq : q ≠ 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδq : δ ≤ |q| / 2) :
    HasLaplacePair (Z (s2pPrior ![0, 0, q, 0, 0] δ) s2pLoss) (5 / 2) 2 := by
  convert s2p_pair_of_spare hδ (spare_bothOut_pair hq hδ hδ1 hδq) using 1; norm_num

/-- **(out, both) total: `(5/2, 1)`.** -/
theorem s2p_outBoth (ha : a ≠ 0) (hδ : 0 < δ) (hδa : δ ≤ |a| / 2) :
    HasLaplacePair (Z (s2pPrior ![a, 0, 0, 0, 0] δ) s2pLoss) (5 / 2) 1 := by
  convert s2p_pair_of_spare hδ (spare_outBoth_pair ha hδ hδa) using 1; norm_num

/-- **S2′'s headline dichotomy.** The same loss in the same parameter space has pair `(3, 1)` at
(L1 dead-out, L2 dead-in) and `(5/2, 1)` at the mirror arrangement (L1 dead-in, L2 dead-out). By
uniqueness of the pair, the (out, in) free energy does **not** have the (in, out) pair. -/
theorem outIn_ne_inOut (ha : a ≠ 0) (hc : c ≠ 0) (hB : B ≠ 0) (hq : q ≠ 0) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hδa : δ ≤ |a| / 2) (hδc : δ ≤ |c| / 2) (hδB : δ ≤ |B| / 2)
    (hδq : δ ≤ |q| / 2) :
    HasLaplacePair (Z (s2pPrior ![a, 0, 0, 0, c] δ) s2pLoss) 3 1 ∧
      HasLaplacePair (Z (s2pPrior ![0, B, q, r, 0] δ) s2pLoss) (5 / 2) 1 ∧
      ¬ HasLaplacePair (Z (s2pPrior ![a, 0, 0, 0, c] δ) s2pLoss) (5 / 2) 1 := by
  have h1 := s2p_outIn ha hc hδ hδa hδc
  refine ⟨h1, s2p_inOut hB hq hδ hδ1 hδB hδq, fun h => ?_⟩
  have := (h1.unique h).1
  norm_num at this

end S2prime

/-! ### S2″ and the hunt: regular ⊕ residual, in the source's local coordinates -/

/-- `n` regular coordinates plus a residual loss `R`. -/
def regPlus {β : Type*} (n : ℕ) (R : β → ℝ) (p : (Fin n → ℝ) × β) : ℝ := regLoss n p.1 + R p.2

/-- The prior: the box around `0` in the regular coordinates, `ν` in the residual ones. -/
noncomputable def regPrior {β : Type*} [MeasurableSpace β] (n : ℕ) (δ : ℝ) (ν : Measure β) :
    Measure ((Fin n → ℝ) × β) :=
  (volume.restrict (box δ)).prod ν

/-- `|t|^n = tⁿ` for even `n`. -/
theorem even_abs_rpow {t : ℝ} {n : ℕ} (hn : Even n) : |t| ^ (n : ℝ) = t ^ n := by
  rw [Real.rpow_natCast, hn.pow_abs]

/-- The duplicate residual `(ε²)`: loss `ε⁴` (M1, M4). -/
def dupLoss (x : Fin 1 → ℝ) : ℝ := x 0 ^ 4

/-- `(ε²)` has pair `(1/4, 1)`. -/
theorem dupLoss_pair {δ : ℝ} (hδ : 0 < δ) :
    HasLaplacePair (Z (volume.restrict (box δ)) dupLoss) (1 / 4) 1 := by
  have h := pair_of_powΓ (s := Finset.univ) (k := fun _ => 4) Finset.univ_nonempty
    (fun _ _ => by norm_num) hδ (K := dupLoss) (by unfold dupLoss; fun_prop) (c := 1) (C := 1)
    one_pos (fun y _ => ?_) (fun y _ => ?_)
  · convert h using 1; simp
  all_goals simp only [Fin.sum_univ_one, dupLoss, one_mul]
  all_goals rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, even_abs_rpow (by decide)]

/-- The full-square residual `(w, p)²`: loss `w⁴ + w²p² + p⁴` (M2; hunt T4 with `(g, ε)`). -/
def sqIdealLoss (z : Fin 2 → ℝ) : ℝ := z 0 ^ 4 + z 0 ^ 2 * z 1 ^ 2 + z 1 ^ 4

/-- `(w, p)²` has pair `(1/2, 1)`. -/
theorem sqIdealLoss_pair {δ : ℝ} (hδ : 0 < δ) :
    HasLaplacePair (Z (volume.restrict (box δ)) sqIdealLoss) (1 / 2) 1 := by
  have h := pair_of_powΓ (s := Finset.univ) (k := fun _ => 4) Finset.univ_nonempty
    (fun _ _ => by norm_num) hδ (K := sqIdealLoss) (by unfold sqIdealLoss; fun_prop) (c := 1)
    (C := 3 / 2) one_pos (fun y _ => ?_) (fun y _ => ?_)
  · convert h using 1; simp; norm_num
  all_goals simp only [Fin.sum_univ_two, sqIdealLoss]
  all_goals rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, even_abs_rpow (by decide),
    even_abs_rpow (by decide)]
  · nlinarith [mul_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1))]
  · nlinarith [sq_nonneg (y 0 ^ 2 - y 1 ^ 2)]

/-- The coupled residual `(ε², ρε)` in `(ε, ρ) = (z 0, z 1)`: loss `ε⁴ + ρ²ε²` (M3, M3′). -/
def cplLoss (z : Fin 2 → ℝ) : ℝ := z 0 ^ 4 + z 1 ^ 2 * z 0 ^ 2

/-- M3's exponent set at `ρ = 0`: `Γ = {(4, 0), (2, 2)}`. -/
noncomputable def ΓM3 : Finset (Fin 2 → ℝ) := {![4, 0], ![2, 2]}

/-- The exponents of `ΓM3` are nonnegative. -/
theorem ΓM3_nonneg : ∀ α ∈ ΓM3, ∀ i, 0 ≤ α i := by
  intro α hα i; simp only [ΓM3, Finset.mem_insert, Finset.mem_singleton] at hα
  rcases hα with rfl | rfl <;> fin_cases i <;> norm_num

/-- M3: `t* = 2`. -/
theorem newtonDist_M3 : newtonDist ΓM3 = 2 := by
  refine newtonDist_eq (u := ![1 / 2, 1 / 2]) ⟨fun i => by fin_cases i <;> norm_num,
    by simp [Fin.sum_univ_two]; norm_num, ?_⟩ ?_
  · intro α hα; simp only [ΓM3, Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> simp [Fin.sum_univ_two] <;> norm_num
  · rintro t u ⟨h0, h1, h2⟩
    have a2 := h2 ![2, 2] (by simp [ΓM3])
    simp [Fin.sum_univ_two] at h1 a2
    linarith

/-- M3: `O` is a segment. -/
theorem optWeights_M3 : optWeights ΓM3 = segment ℝ ![1 / 2, 1 / 2] ![1, 0] := by
  ext u
  rw [optWeights, newtonDist_M3]
  simp only [IsNewtonCert, ΓM3, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq, Fin.sum_univ_two, mem_ofPred_eq]
  constructor
  · rintro ⟨h0, h1, a1, a2⟩
    norm_num at a1 a2
    have := h0 0; have := h0 1
    refine ⟨2 * u 1, 2 * u 0 - 1, by linarith, by linarith, by linarith, ?_⟩
    funext i; fin_cases i <;> simp <;> linarith
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨fun i => by fin_cases i <;> simp [ha, hb, add_nonneg], by simp; linarith,
      by simp; nlinarith, by simp; nlinarith⟩

/-- M3: `m = 2`. -/
theorem newtonMult_M3 : newtonMult ΓM3 = 2 :=
  newtonMult_eq_two optWeights_M3 (fun h => by have := congrFun h 1; norm_num at this)

/-- M3: the monomial sum is the loss `ε⁴ + ε²ρ²`. -/
theorem monoSum_M3 (y : Fin 2 → ℝ) : monoSum ΓM3 y = y 0 ^ 4 + y 0 ^ 2 * y 1 ^ 2 := by
  rw [monoSum, ΓM3, Finset.sum_pair (fun h => absurd (congrFun h 0) (by norm_num))]
  simp only [monomial, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Real.rpow_zero, mul_one]
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, even_abs_rpow (by decide), Real.rpow_two,
    Real.rpow_two, sq_abs, sq_abs]

/-- **M3 (the slice `ρ = 0`)**: `(ε², ρε)` at `(0, 0)` has pair `(1/2, 2)`. -/
theorem cplLoss_slice_pair {δ : ℝ} (hδ : 0 < δ) :
    HasLaplacePair (Z (volume.restrict (box δ)) cplLoss) (1 / 2) 2 := by
  have h := pair_of_Γ ΓM3_nonneg (by rw [newtonDist_M3]; norm_num) hδ (K := cplLoss)
    (by unfold cplLoss; fun_prop) (c := 1) (C := 1) one_pos
    (fun y _ => by rw [monoSum_M3, cplLoss]; linarith [mul_comm (y 1 ^ 2) (y 0 ^ 2)])
    (fun y _ => by rw [monoSum_M3, cplLoss]; linarith [mul_comm (y 1 ^ 2) (y 0 ^ 2)])
  rw [one_div]; rwa [newtonDist_M3, newtonMult_M3] at h

/-- **M3′ (generic `ρ* ≠ 0`)**: `(ε², ρε)` at `(0, ρ*)` is `≍ ε²`, pair `(1/2, 1)`. The live
downstream spare linearizes the duplicate. -/
theorem cplLoss_generic_pair {ρ δ : ℝ} (hρ : ρ ≠ 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδρ : δ ≤ |ρ| / 2) :
    HasLaplacePair (Z (volume.restrict {z | z - ![0, ρ] ∈ box δ}) cplLoss) (1 / 2) 1 := by
  rw [Z_translate]
  have h := pair_of_powΓ (s := {0}) (k := fun _ => 2) (by simp) (fun _ _ => two_pos) hδ
    (K := fun y => cplLoss (![0, ρ] + y)) ((by unfold cplLoss; fun_prop : Measurable cplLoss).comp
      (measurable_const_add _)) (c := ρ ^ 2 / 4) (C := 1 + 9 * ρ ^ 2 / 4) (by positivity) ?_ ?_
  · convert h using 1; simp
  all_goals intro y hy
  all_goals rw [sum_abs_rpow_two, Finset.sum_singleton]
  all_goals simp only [cplLoss, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, zero_add]
  all_goals have hρ' := unit_sq_bounds hδρ (abs_le_of_mem_box hy 1)
  all_goals have h0 := sq_le_one_of_mem_box hδ1 hy 0
  · nlinarith [mul_le_mul_of_nonneg_right hρ'.1 (sq_nonneg (y 0)), sq_nonneg (y 0 ^ 2)]
  · nlinarith [mul_le_mul_of_nonneg_right hρ'.2 (sq_nonneg (y 0)),
      mul_le_mul_of_nonneg_right h0 (sq_nonneg (y 0))]

section S2pp

variable {δ : ℝ}

/-- **M1 and M4: `(9/4, 1)`** (4 regular ⊕ `(ε²)`). -/
theorem m1_m4_pair (hδ : 0 < δ) :
    HasLaplacePair (Z (regPrior 4 δ (volume.restrict (box δ))) (regPlus 4 dupLoss)) (9 / 4) 1 := by
  have := regular_add_pair (n := 4) (by norm_num) hδ (by unfold dupLoss; fun_prop)
    (dupLoss_pair hδ)
  rw [show (9 / 4 : ℝ) = ((4 : ℕ) : ℝ) / 2 + 1 / 4 by norm_num]; exact this

/-- **M2: `(5/2, 1)`** (4 regular ⊕ `(w, p)²`). -/
theorem m2_pair (hδ : 0 < δ) :
    HasLaplacePair (Z (regPrior 4 δ (volume.restrict (box δ))) (regPlus 4 sqIdealLoss))
      (5 / 2) 1 := by
  have := regular_add_pair (n := 4) (by norm_num) hδ (by unfold sqIdealLoss; fun_prop)
    (sqIdealLoss_pair hδ)
  rw [show (5 / 2 : ℝ) = ((4 : ℕ) : ℝ) / 2 + 1 / 2 by norm_num]; exact this

/-- **M3, the special slice `ρ = 0`: `(5/2, 2)`** (4 regular ⊕ `(ε², ρε)` at `(0, 0)`). -/
theorem m3_pair (hδ : 0 < δ) :
    HasLaplacePair (Z (regPrior 4 δ (volume.restrict (box δ))) (regPlus 4 cplLoss)) (5 / 2) 2 := by
  have := regular_add_pair (n := 4) (by norm_num) hδ (by unfold cplLoss; fun_prop)
    (cplLoss_slice_pair hδ)
  rw [show (5 / 2 : ℝ) = ((4 : ℕ) : ℝ) / 2 + 1 / 2 by norm_num]; exact this

/-- **M3′, generic `ρ* ≠ 0`: `(5/2, 1)`** (4 regular ⊕ `(ε², ρε)` at `(0, ρ*)`). -/
theorem m3'_pair {ρ : ℝ} (hρ : ρ ≠ 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδρ : δ ≤ |ρ| / 2) :
    HasLaplacePair (Z (regPrior 4 δ (volume.restrict {z | z - ![0, ρ] ∈ box δ}))
      (regPlus 4 cplLoss)) (5 / 2) 1 := by
  have := regular_add_pair (n := 4) (by norm_num) hδ (by unfold cplLoss; fun_prop)
    (cplLoss_generic_pair hρ hδ hδ1 hδρ)
  rw [show (5 / 2 : ℝ) = ((4 : ℕ) : ℝ) / 2 + 1 / 2 by norm_num]; exact this

/-- **Hunt T4, generic `(dup, dup)`: `(2, 1)`** (3 regular ⊕ `(g, ε)²`). -/
theorem dupDup_pair (hδ : 0 < δ) :
    HasLaplacePair (Z (regPrior 3 δ (volume.restrict (box δ))) (regPlus 3 sqIdealLoss)) 2 1 := by
  have := regular_add_pair (n := 3) (by norm_num) hδ (by unfold sqIdealLoss; fun_prop)
    (sqIdealLoss_pair hδ)
  rw [show (2 : ℝ) = ((3 : ℕ) : ℝ) / 2 + 1 / 2 by norm_num]; exact this

/-- **S2″'s headline dichotomy.** At equal codimension (5), M4 (L1 dead-in, L2 duplicate) has
`(9/4, 1)` and M3′ (L1 duplicate, L2 input cancelled) has `(5/2, 1)`: the arrangement changes `λ`
through the *order* of the duplicate's degeneracy, not through codimension. (The reduction of each
realization to its model is on paper.) -/
theorem m4_ne_m3' {ρ : ℝ} (hρ : ρ ≠ 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδρ : δ ≤ |ρ| / 2) :
    HasLaplacePair (Z (regPrior 4 δ (volume.restrict (box δ))) (regPlus 4 dupLoss)) (9 / 4) 1 ∧
      HasLaplacePair (Z (regPrior 4 δ (volume.restrict {z | z - ![0, ρ] ∈ box δ}))
        (regPlus 4 cplLoss)) (5 / 2) 1 ∧
      (9 / 4 : ℝ) ≠ 5 / 2 :=
  ⟨m1_m4_pair hδ, m3'_pair hρ hδ hδ1 hδρ, by norm_num⟩

end S2pp

end SLT.Zoo.MLP
