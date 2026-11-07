/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Laplace.Rate

/-!
# Laplace pairs `F(N) ≍ N^{-λ} (log N)^{m-1}`

For `F : ℝ → ℝ≥0∞` (typically `Z(N) = ∫ e^{-N K} dν`):

* `LaplaceLower F λ m`: `F(N) ≥ c · rate λ m N` eventually, for some `c > 0`;
* `LaplaceUpper F λ m`: `F(N) ≤ C · rate λ m N` eventually;
* `HasLaplacePair F λ m`: `1 ≤ m` and both bounds. This is the *learning pair* (λ, m).

The API is about the function `F` alone: monotonicity, constants, rescaling `N ↦ bN`, domination,
exponential decay, sums (the dominant pair wins: `λ = min`, `m = max` among minimisers), products
(`(λ₁+λ₂, m₁+m₂-1)`), and **uniqueness** of `(λ, m)`.

## Alignment with existing libraries
* `vector-slt-lean`: `SLT.HasLaplacePair` there has the bodies of `laplaceLower_iff`/`laplaceUpper_iff`
  below and no `1 ≤ m`. See `hasLaplacePair_iff_bounds`.
* `residual-slt-in-a-haystack`: `ResidualSLT.HasLaplaceOrder` has exactly the body of
  `SLT.HasLaplaceOrder` below (real-valued). See `hasLaplacePair_ofReal_iff`.
* Timaeus `grammar`: `LaplaceTheta μ f λ q` is `(N ↦ ∫ e^{-N f} dμ) =Θ[atTop] powerLogRate λ q` with
  `q = m - 1`. See `hasLaplacePair_ofReal_iff_isTheta`.
-/

@[expose] public section

namespace SLT

open Filter Asymptotics Real Finset
open scoped ENNReal

variable {F G : ℝ → ℝ≥0∞} {lam lam' : ℝ} {m m' : ℕ}

/-- `F(N) ≥ c N^{-λ} (log N)^{m-1}` eventually, for some `c > 0`. -/
def LaplaceLower (F : ℝ → ℝ≥0∞) (lam : ℝ) (m : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ N in atTop, ENNReal.ofReal (c * rate lam m N) ≤ F N

/-- `F(N) ≤ C N^{-λ} (log N)^{m-1}` eventually. -/
def LaplaceUpper (F : ℝ → ℝ≥0∞) (lam : ℝ) (m : ℕ) : Prop :=
  ∃ C : ℝ, ∀ᶠ N in atTop, F N ≤ ENNReal.ofReal (C * rate lam m N)

/-- **The learning pair** `(λ, m)`: `F(N) ≍ N^{-λ} (log N)^{m-1}`, with `m ≥ 1`. -/
def HasLaplacePair (F : ℝ → ℝ≥0∞) (lam : ℝ) (m : ℕ) : Prop :=
  1 ≤ m ∧ LaplaceLower F lam m ∧ LaplaceUpper F lam m

/-! ### Explicit-constant forms -/

theorem laplaceLower_iff : LaplaceLower F lam m ↔ ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N, N₀ ≤ N →
    ENNReal.ofReal (c * N ^ (-lam) * Real.log N ^ (m - 1)) ≤ F N := by
  simp only [LaplaceLower, eventually_atTop, rate, mul_assoc]

theorem laplaceUpper_iff : LaplaceUpper F lam m ↔ ∃ C : ℝ, ∃ N₀ : ℝ, ∀ N, N₀ ≤ N →
    F N ≤ ENNReal.ofReal (C * N ^ (-lam) * Real.log N ^ (m - 1)) := by
  simp only [LaplaceUpper, eventually_atTop, rate, mul_assoc]

/-- `HasLaplacePair` is `1 ≤ m` plus the body of `vector-slt-lean`'s `SLT.HasLaplacePair`. -/
theorem hasLaplacePair_iff_bounds : HasLaplacePair F lam m ↔ 1 ≤ m ∧
    ((∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N, N₀ ≤ N →
      ENNReal.ofReal (c * N ^ (-lam) * Real.log N ^ (m - 1)) ≤ F N) ∧
    (∃ C : ℝ, ∃ N₀ : ℝ, ∀ N, N₀ ≤ N →
      F N ≤ ENNReal.ofReal (C * N ^ (-lam) * Real.log N ^ (m - 1)))) := by
  rw [HasLaplacePair, laplaceLower_iff, laplaceUpper_iff]

/-! ### Basic API -/

theorem LaplaceUpper.exists_pos (h : LaplaceUpper F lam m) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in atTop, F N ≤ ENNReal.ofReal (C * rate lam m N) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 1, by positivity, ?_⟩
  filter_upwards [hC, eventually_rate_nonneg lam m] with N h1 h2
  exact h1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) h2))

theorem LaplaceUpper.eventually_lt_top (h : LaplaceUpper F lam m) : ∀ᶠ N in atTop, F N < ⊤ := by
  obtain ⟨C, hC⟩ := h
  filter_upwards [hC] with N h using h.trans_lt ENNReal.ofReal_lt_top

theorem LaplaceLower.mono (h : LaplaceLower F lam m) (hFG : ∀ᶠ N in atTop, F N ≤ G N) :
    LaplaceLower G lam m := by
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, by filter_upwards [h, hFG] with N h1 h2 using h1.trans h2⟩

theorem LaplaceUpper.mono (h : LaplaceUpper G lam m) (hFG : ∀ᶠ N in atTop, F N ≤ G N) :
    LaplaceUpper F lam m := by
  obtain ⟨C, h⟩ := h
  exact ⟨C, by filter_upwards [h, hFG] with N h1 h2 using h2.trans h1⟩

theorem HasLaplacePair.congr (h : HasLaplacePair F lam m) (hFG : F =ᶠ[atTop] G) :
    HasLaplacePair G lam m :=
  ⟨h.1, h.2.1.mono hFG.le, h.2.2.mono hFG.symm.le⟩

theorem LaplaceLower.const_mul {a : ℝ≥0∞} (ha : a ≠ 0) (ha' : a ≠ ⊤) (h : LaplaceLower F lam m) :
    LaplaceLower (fun N => a * F N) lam m := by
  obtain ⟨c, hc, h⟩ := h
  have hpos : 0 < a.toReal := ENNReal.toReal_pos ha ha'
  refine ⟨a.toReal * c, by positivity, ?_⟩
  filter_upwards [h] with N h1
  rw [mul_assoc, ENNReal.ofReal_mul hpos.le, ENNReal.ofReal_toReal ha']
  gcongr

theorem LaplaceUpper.const_mul {a : ℝ≥0∞} (ha' : a ≠ ⊤) (h : LaplaceUpper F lam m) :
    LaplaceUpper (fun N => a * F N) lam m := by
  obtain ⟨C, -, h⟩ := h.exists_pos
  refine ⟨a.toReal * C, ?_⟩
  filter_upwards [h] with N h1
  rw [mul_assoc, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha']
  gcongr

theorem HasLaplacePair.const_mul {a : ℝ≥0∞} (ha : a ≠ 0) (ha' : a ≠ ⊤)
    (h : HasLaplacePair F lam m) : HasLaplacePair (fun N => a * F N) lam m :=
  ⟨h.1, h.2.1.const_mul ha ha', h.2.2.const_mul ha'⟩

/-! ### Rescaling `N ↦ b N` -/

theorem LaplaceLower.comp_mul {b : ℝ} (hb : 0 < b) (h : LaplaceLower F lam m) :
    LaplaceLower (fun N => F (b * N)) lam m := by
  obtain ⟨c, hc, h⟩ := h
  have ht : Tendsto (fun N : ℝ => b * N) atTop atTop := tendsto_id.const_mul_atTop hb
  refine ⟨c * (b ^ (-lam) * (1 / 2) ^ (m - 1)), by positivity, ?_⟩
  filter_upwards [ht.eventually h, rate_comp_mul_bounds lam m hb] with N h1 h2
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) h1
  calc c * (b ^ (-lam) * (1 / 2) ^ (m - 1)) * rate lam m N
      = c * (b ^ (-lam) * (1 / 2) ^ (m - 1) * rate lam m N) := by ring
    _ ≤ c * rate lam m (b * N) := mul_le_mul_of_nonneg_left h2.1 hc.le

theorem LaplaceUpper.comp_mul {b : ℝ} (hb : 0 < b) (h : LaplaceUpper F lam m) :
    LaplaceUpper (fun N => F (b * N)) lam m := by
  obtain ⟨C, hC, h⟩ := h.exists_pos
  have ht : Tendsto (fun N : ℝ => b * N) atTop atTop := tendsto_id.const_mul_atTop hb
  refine ⟨C * (b ^ (-lam) * 2 ^ (m - 1)), ?_⟩
  filter_upwards [ht.eventually h, rate_comp_mul_bounds lam m hb] with N h1 h2
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  calc C * rate lam m (b * N) ≤ C * (b ^ (-lam) * 2 ^ (m - 1) * rate lam m N) :=
        mul_le_mul_of_nonneg_left h2.2 hC.le
    _ = _ := by ring

theorem HasLaplacePair.comp_mul {b : ℝ} (hb : 0 < b) (h : HasLaplacePair F lam m) :
    HasLaplacePair (fun N => F (b * N)) lam m :=
  ⟨h.1, h.2.1.comp_mul hb, h.2.2.comp_mul hb⟩

/-! ### Domination and exponential decay -/

/-- An upper bound at a dominated rate is an upper bound at the dominating rate. -/
theorem LaplaceUpper.of_dominates (h : LaplaceUpper F lam' m') (hd : Dominates lam m lam' m') :
    LaplaceUpper F lam m := by
  obtain ⟨C, hC, h⟩ := h.exists_pos
  exact ⟨C, by
    filter_upwards [h, rate_le_of_dominates hd] with N h1 h2
    exact h1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h2 hC.le))⟩

/-- A lower bound at a dominating rate is a lower bound at the dominated rate. -/
theorem LaplaceLower.of_dominates (h : LaplaceLower F lam m) (hd : Dominates lam m lam' m') :
    LaplaceLower F lam' m' := by
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, by
    filter_upwards [h, rate_le_of_dominates hd] with N h1 h2
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h2 hc.le)).trans h1⟩

/-- **Exponentially small terms are below every rate.** -/
theorem laplaceUpper_of_exp {a C : ℝ} (ha : 0 < a)
    (h : ∀ᶠ N in atTop, F N ≤ ENNReal.ofReal (C * Real.exp (-a * N))) (lam : ℝ) (m : ℕ) :
    LaplaceUpper F lam m := by
  have hb := (exp_neg_isLittleO_rate ha lam m).bound one_pos
  refine ⟨max C 0, ?_⟩
  filter_upwards [h, hb, eventually_rate_nonneg lam m] with N h1 h2 h3
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg h3, one_mul] at h2
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  calc C * Real.exp (-a * N) ≤ max C 0 * Real.exp (-a * N) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C 0 * rate lam m N := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)

/-! ### Sums: the dominant pair wins -/

theorem laplaceUpper_zero (lam : ℝ) (m : ℕ) : LaplaceUpper (fun _ => 0) lam m :=
  ⟨0, Eventually.of_forall fun _ => zero_le⟩

theorem LaplaceUpper.add (hF : LaplaceUpper F lam m) (hG : LaplaceUpper G lam m) :
    LaplaceUpper (fun N => F N + G N) lam m := by
  obtain ⟨C₁, hC₁, h₁⟩ := hF.exists_pos
  obtain ⟨C₂, hC₂, h₂⟩ := hG.exists_pos
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂, eventually_rate_nonneg lam m] with N a b r
  calc F N + G N ≤ ENNReal.ofReal (C₁ * rate lam m N) + ENNReal.ofReal (C₂ * rate lam m N) :=
        add_le_add a b
    _ = ENNReal.ofReal (C₁ * rate lam m N + C₂ * rate lam m N) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ = _ := by rw [add_mul]

theorem LaplaceUpper.finset_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ≥0∞}
    (h : ∀ i ∈ s, LaplaceUpper (F i) lam m) : LaplaceUpper (fun N => ∑ i ∈ s, F i N) lam m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using laplaceUpper_zero lam m
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem LaplaceLower.le_sum {ι : Type*} {s : Finset ι} {F : ι → ℝ → ℝ≥0∞} {i : ι} (hi : i ∈ s)
    (h : LaplaceLower (F i) lam m) : LaplaceLower (fun N => ∑ j ∈ s, F j N) lam m :=
  h.mono (Eventually.of_forall fun N => Finset.single_le_sum (f := fun j => F j N) (fun _ _ => zero_le) hi)

/-- **Finite sums, dominant-term form.** If `F i₀` has a lower bound at `(λ, m)`, and every term
has an upper bound at a rate dominated by `(λ, m)`, then the sum has the pair `(λ, m)`. Terms
with exponential decay are allowed (`laplaceUpper_of_exp`). -/
theorem hasLaplacePair_finset_sum {ι : Type*} {s : Finset ι} {F : ι → ℝ → ℝ≥0∞} {i₀ : ι}
    (hi₀ : i₀ ∈ s) (hm : 1 ≤ m) (hlow : LaplaceLower (F i₀) lam m) {lam' : ι → ℝ} {m' : ι → ℕ}
    (hup : ∀ i ∈ s, LaplaceUpper (F i) (lam' i) (m' i))
    (hdom : ∀ i ∈ s, Dominates lam m (lam' i) (m' i)) :
    HasLaplacePair (fun N => ∑ i ∈ s, F i N) lam m :=
  ⟨hm, hlow.le_sum hi₀, LaplaceUpper.finset_sum s fun i hi => (hup i hi).of_dominates (hdom i hi)⟩

/-- **Finite sums, min/max form.** A nonempty finite sum of terms with pairs `(λᵢ, mᵢ)` has the
pair `(λ, m)` with `λ = minᵢ λᵢ` and `m = max {mᵢ : λᵢ = λ}`. -/
theorem exists_hasLaplacePair_finset_sum {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {F : ι → ℝ → ℝ≥0∞} {lam : ι → ℝ} {m : ι → ℕ} (h : ∀ i ∈ s, HasLaplacePair (F i) (lam i) (m i)) :
    ∃ i₀ ∈ s, (∀ i ∈ s, lam i₀ ≤ lam i) ∧ (∀ i ∈ s, lam i = lam i₀ → m i ≤ m i₀) ∧
      HasLaplacePair (fun N => ∑ i ∈ s, F i N) (lam i₀) (m i₀) := by
  classical
  obtain ⟨j, hj, hjmin⟩ := s.exists_min_image lam hs
  have hs' : (s.filter fun i => lam i = lam j).Nonempty := ⟨j, mem_filter.mpr ⟨hj, rfl⟩⟩
  obtain ⟨i₀, hi₀, hmax⟩ := (s.filter fun i => lam i = lam j).exists_max_image m hs'
  obtain ⟨hi₀s, hi₀l⟩ := mem_filter.mp hi₀
  have hmin : ∀ i ∈ s, lam i₀ ≤ lam i := fun i hi => by rw [hi₀l]; exact hjmin i hi
  have hmaxm : ∀ i ∈ s, lam i = lam i₀ → m i ≤ m i₀ := fun i hi hl =>
    hmax i (mem_filter.mpr ⟨hi, hl.trans hi₀l⟩)
  refine ⟨i₀, hi₀s, hmin, hmaxm, hasLaplacePair_finset_sum hi₀s (h i₀ hi₀s).1 (h i₀ hi₀s).2.1
    (fun i hi => (h i hi).2.2) fun i hi => ?_⟩
  rcases (hmin i hi).lt_or_eq with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, hmaxm i hi heq.symm⟩

/-! ### Products: `(λ₁ + λ₂, m₁ + m₂ - 1)` -/

theorem hasLaplacePair_one : HasLaplacePair (fun _ => 1) 0 1 :=
  ⟨le_rfl, ⟨1, one_pos, Eventually.of_forall fun N => by simp [rate_zero_one]⟩,
    ⟨1, Eventually.of_forall fun N => by simp [rate_zero_one]⟩⟩

theorem HasLaplacePair.mul {l₁ l₂ : ℝ} {m₁ m₂ : ℕ} (h₁ : HasLaplacePair F l₁ m₁)
    (h₂ : HasLaplacePair G l₂ m₂) :
    HasLaplacePair (fun N => F N * G N) (l₁ + l₂) (m₁ + m₂ - 1) := by
  obtain ⟨hm₁, ⟨a₁, ha₁, A₁⟩, hU₁⟩ := h₁
  obtain ⟨hm₂, ⟨a₂, ha₂, A₂⟩, hU₂⟩ := h₂
  obtain ⟨b₁, hb₁, B₁⟩ := hU₁.exists_pos
  obtain ⟨b₂, hb₂, B₂⟩ := hU₂.exists_pos
  refine ⟨by omega, ⟨a₁ * a₂, by positivity, ?_⟩, ⟨b₁ * b₂, ?_⟩⟩
  · filter_upwards [A₁, A₂, eventually_gt_atTop 0, eventually_rate_nonneg l₁ m₁,
      eventually_rate_nonneg l₂ m₂] with N h1 h2 hN r1 r2
    rw [rate_add hm₁ hm₂ hN, show a₁ * a₂ * (rate l₁ m₁ N * rate l₂ m₂ N) =
      (a₁ * rate l₁ m₁ N) * (a₂ * rate l₂ m₂ N) by ring, ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' h1 h2
  · filter_upwards [B₁, B₂, eventually_gt_atTop 0, eventually_rate_nonneg l₁ m₁,
      eventually_rate_nonneg l₂ m₂] with N h1 h2 hN r1 r2
    rw [rate_add hm₁ hm₂ hN, show b₁ * b₂ * (rate l₁ m₁ N * rate l₂ m₂ N) =
      (b₁ * rate l₁ m₁ N) * (b₂ * rate l₂ m₂ N) by ring, ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' h1 h2

/-- **Finite products**: `∏ Fᵢ` has the pair `(Σ λᵢ, Σ (mᵢ - 1) + 1)`. -/
theorem HasLaplacePair.finset_prod {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ≥0∞}
    {lam : ι → ℝ} {m : ι → ℕ} (h : ∀ i ∈ s, HasLaplacePair (F i) (lam i) (m i)) :
    HasLaplacePair (fun N => ∏ i ∈ s, F i N) (∑ i ∈ s, lam i) (∑ i ∈ s, (m i - 1) + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasLaplacePair_one
  | insert a s ha ih =>
    have ha' := h a (mem_insert_self a s)
    have h' := ha'.mul (ih fun i hi => h i (mem_insert_of_mem hi))
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    have e : m a - 1 + ∑ i ∈ s, (m i - 1) + 1 = m a + (∑ i ∈ s, (m i - 1) + 1) - 1 := by
      have := ha'.1; omega
    rw [e]; exact h'

/-! ### Uniqueness of the pair -/

/-- A lower bound at `(λ, m)` and an upper bound at `(λ', m')` force `(λ', m')` to dominate. -/
theorem dominates_of_lower_upper (hm' : 1 ≤ m') (hl : LaplaceLower F lam m)
    (hu : LaplaceUpper F lam' m') : Dominates lam' m' lam m := by
  by_contra hnd
  have hstrict : lam < lam' ∨ (lam = lam' ∧ m' < m) := by
    simp only [Dominates, not_or, not_and, not_le, not_lt] at hnd
    rcases hnd.1.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hnd.2 h.symm⟩
  obtain ⟨c, hc, hl⟩ := hl
  obtain ⟨C, hC, hu⟩ := hu.exists_pos
  have ho := (rate_isLittleO hm' hstrict).bound (show 0 < c / (2 * C) by positivity)
  obtain ⟨N, h1, h2, h3, h4, h5⟩ := (hl.and (hu.and (ho.and ((eventually_rate_pos lam m).and
    (eventually_rate_nonneg lam' m'))))).exists
  have h12 : c * rate lam m N ≤ C * rate lam' m' N :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (h1.trans h2)
  rw [Real.norm_of_nonneg h5, Real.norm_of_nonneg h4.le] at h3
  have : C * rate lam' m' N ≤ c / 2 * rate lam m N := by
    calc C * rate lam' m' N ≤ C * (c / (2 * C) * rate lam m N) :=
          mul_le_mul_of_nonneg_left h3 hC.le
      _ = c / 2 * rate lam m N := by field_simp
  nlinarith

/-- **Uniqueness**: a function has at most one Laplace pair. -/
theorem HasLaplacePair.unique (h : HasLaplacePair F lam m) (h' : HasLaplacePair F lam' m') :
    lam = lam' ∧ m = m' := by
  have d1 := dominates_of_lower_upper h'.1 h.2.1 h'.2.2
  have d2 := dominates_of_lower_upper h.1 h'.2.1 h.2.2
  rcases d1 with d1 | ⟨d1, d1'⟩ <;> rcases d2 with d2 | ⟨d2, d2'⟩
  · linarith
  · linarith
  · linarith
  · exact ⟨d2, by omega⟩

/-! ### Real-valued and `IsTheta` forms -/

/-- The body of `ResidualSLT.HasLaplaceOrder` (scalar library), verbatim with `laplaceRate = rate`. -/
def HasLaplaceOrder (ℓ : ℝ) (m : ℕ) (Z : ℝ → ℝ) : Prop :=
  0 < m ∧ ∃ c C N₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
    c * rate ℓ m N ≤ Z N ∧ Z N ≤ C * rate ℓ m N

/-- **Bridge to the scalar library**: for real `Z`, the pair of `ofReal ∘ Z` is `HasLaplaceOrder`. -/
theorem hasLaplacePair_ofReal_iff {Z : ℝ → ℝ} :
    HasLaplacePair (fun N => ENNReal.ofReal (Z N)) lam m ↔ HasLaplaceOrder lam m Z := by
  constructor
  · rintro ⟨hm, ⟨c, hc, hl⟩, hu⟩
    obtain ⟨C, hC, hu⟩ := hu.exists_pos
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hl.and (hu.and (eventually_gt_atTop 1)))
    refine ⟨by omega, c, C, max N₀ 2, hc, hC, lt_of_lt_of_le one_lt_two (le_max_right _ _),
      fun N hN => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hN₀ N ((le_max_left _ _).trans hN)
    have hr := rate_pos lam m h3
    refine ⟨?_, (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2⟩
    rcases ENNReal.ofReal_le_ofReal_iff'.mp h1 with h | h
    · exact h
    · exact absurd h (not_le.mpr (by positivity))
  · rintro ⟨hm, c, C, N₀, hc, -, -, h⟩
    refine ⟨by omega, ⟨c, hc, ?_⟩, ⟨C, ?_⟩⟩ <;> filter_upwards [eventually_ge_atTop N₀] with N hN
    · exact ENNReal.ofReal_le_ofReal (h N hN).1
    · exact ENNReal.ofReal_le_ofReal (h N hN).2

/-- **Bridge to `IsTheta`** (grammar's `LaplaceTheta` form): for eventually nonnegative real `Z`
and `m ≥ 1`, the pair of `ofReal ∘ Z` is `Z =Θ[atTop] rate λ m`. -/
theorem hasLaplacePair_ofReal_iff_isTheta {Z : ℝ → ℝ} (hZ : ∀ᶠ N in atTop, 0 ≤ Z N)
    (hm : 1 ≤ m) :
    HasLaplacePair (fun N => ENNReal.ofReal (Z N)) lam m ↔ Z =Θ[atTop] rate lam m := by
  rw [hasLaplacePair_ofReal_iff]
  constructor
  · rintro ⟨-, c, C, N₀, hc, hC, -, h⟩
    have hev : ∀ᶠ N in atTop, c * rate lam m N ≤ Z N ∧ Z N ≤ C * rate lam m N :=
      (eventually_ge_atTop N₀).mono fun N hN => h N hN
    refine ⟨IsBigO.of_bound C ?_, IsBigO.of_bound c⁻¹ ?_⟩
    · filter_upwards [hev, hZ, eventually_rate_nonneg lam m] with N h1 h2 h3
      rw [Real.norm_of_nonneg h2, Real.norm_of_nonneg h3]; exact h1.2
    · filter_upwards [hev, hZ, eventually_rate_nonneg lam m] with N h1 h2 h3
      rw [Real.norm_of_nonneg h2, Real.norm_of_nonneg h3, le_inv_mul_iff₀ hc]; exact h1.1
  · rintro ⟨hup, hlo⟩
    obtain ⟨C, hC⟩ := hup.bound
    obtain ⟨c, hc⟩ := hlo.bound
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hC.and (hc.and (hZ.and (eventually_gt_atTop 1))))
    refine ⟨by omega, (max c 1)⁻¹, max C 1, max N₀ 2, by positivity, by positivity,
      lt_of_lt_of_le one_lt_two (le_max_right _ _), fun N hN => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := hN₀ N ((le_max_left _ _).trans hN)
    have hr := rate_pos lam m h4
    rw [Real.norm_of_nonneg h3, Real.norm_of_nonneg hr.le] at h1 h2
    refine ⟨?_, h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr.le)⟩
    rw [inv_mul_le_iff₀ (by positivity)]
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) h3)

end SLT
