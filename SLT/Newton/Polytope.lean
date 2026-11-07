/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.Newton.Statement
public import Mathlib.Analysis.Convex.KreinMilman

/-!
# The dual polyhedron and its near-optimal slabs (N2, polyhedral step)

`P = { u ≥ 0 | ⟨α,u⟩ ≥ 1 ∀ α ∈ Γ }` is the dual polyhedron. On `P`, `⟨𝟙,u⟩ ≥ 1/t*`
(`one_dot_ge`). Its near-optimal slabs are `P_η = P ∩ {⟨𝟙,u⟩ ≤ 1/t* + η}`, and the optimal face is
`P_0 = (1/t*)·O`.

**Main result** (`dualSlab_subset`): for small `η ≥ 0`, `P_η ⊆ P_0 + closedBall 0 (C η)`. This is a
Hoffman-type error bound. It is proved without LP duality:
* an extreme point of a finite system `A u ≥ b` has tight rows with trivial joint kernel
  (`eq_zero_of_extremePoint`);
* the vertices of `P` form a finite set, so there is a gap `g > 0` above `1/t*`;
* an extreme point `v` of `P_η` with `η < g` can be slid along a kernel direction `z` (taken from a
  finite set of such directions, so `‖z‖ ≤ C`) down to `v - η z ∈ P_0`;
* Krein–Milman (`closure_convexHull_extremePoints`) finishes it.
-/

@[expose] public section

namespace SLT.Newton

open Set Matrix Metric Filter Topology
open scoped Pointwise

variable {d : ℕ}

/-! ### Finite linear systems -/

section System

variable {R : Type*} [Fintype R] (a : R → Fin d → ℝ) (b : R → ℝ)

/-- The solution set `{u | b r ≤ a r ⬝ᵥ u ∀ r}` of a finite linear system. -/
def sysSet : Set (Fin d → ℝ) := {u | ∀ r, b r ≤ a r ⬝ᵥ u}

omit [Fintype R] in
theorem convex_sysSet : Convex ℝ (sysSet a b) := by
  intro u hu v hv s t hs ht hst r
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left (hu r) hs
  have h2 := mul_le_mul_of_nonneg_left (hv r) ht
  have : b r = s * b r + t * b r := by rw [← add_mul, hst, one_mul]
  linarith

omit [Fintype R] in
theorem isClosed_sysSet : IsClosed (sysSet a b) := by
  have : sysSet a b = ⋂ r, {u | b r ≤ a r ⬝ᵥ u} := by ext; simp [sysSet]
  rw [this]
  refine isClosed_iInter fun r => isClosed_le continuous_const ?_
  show Continuous fun u : Fin d → ℝ => ∑ i, a r i * u i
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)

/-- **Extreme points are basic**: the tight rows at an extreme point have trivial joint kernel. -/
theorem eq_zero_of_extremePoint {v : Fin d → ℝ} (hv : v ∈ (sysSet a b).extremePoints ℝ)
    {z : Fin d → ℝ} (hz : ∀ r, a r ⬝ᵥ v = b r → a r ⬝ᵥ z = 0) : z = 0 := by
  by_contra hz0
  have hvS := hv.1
  -- for small `ε`, `v ± ε z` stay in the system
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ r, b r ≤ a r ⬝ᵥ (v + ε • z) ∧ b r ≤ a r ⬝ᵥ (v - ε • z) := by
    refine eventually_all.2 fun r => ?_
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    by_cases ht : a r ⬝ᵥ v = b r
    · refine Eventually.of_forall fun ε => ?_
      rw [hz r ht, mul_zero, add_zero, sub_zero]; exact ⟨ht.ge, ht.ge⟩
    · have hs : 0 < a r ⬝ᵥ v - b r := sub_pos.mpr (lt_of_le_of_ne (hvS r) (Ne.symm ht))
      have hc : Tendsto (fun ε : ℝ => ε * (a r ⬝ᵥ z)) (𝓝 0) (𝓝 0) := by
        have := (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (a r ⬝ᵥ z)
        simpa using this
      filter_upwards [hc.eventually (Ioo_mem_nhds (neg_lt_zero.mpr hs) hs)] with ε hε
      exact ⟨by linarith [hε.1], by linarith [hε.2]⟩
  obtain ⟨ε, hε, hε0⟩ := (hev.filter_mono nhdsWithin_le_nhds |>.and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have h1 : v - ε • z ∈ sysSet a b := fun r => (hε r).2
  have h2 : v + ε • z ∈ sysSet a b := fun r => (hε r).1
  have hseg : v ∈ openSegment ℝ (v - ε • z) (v + ε • z) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; simp; ring
  have := hv.2 h1 h2 hseg
  have hεz : ε • z = 0 := by rw [sub_eq_self] at this; exact this
  rcases smul_eq_zero.mp hεz with h | h
  · exact absurd h (ne_of_gt hε0)
  · exact hz0 h

end System

/-! ### The dual polyhedron -/

/-- The all-ones vector. -/
def ones : Fin d → ℝ := fun _ => 1

theorem ones_dotProduct (u : Fin d → ℝ) : ones ⬝ᵥ u = ∑ i, u i := by
  simp [ones, dotProduct]

/-- The dual polyhedron `P = { u ≥ 0 | ⟨α,u⟩ ≥ 1 ∀ α ∈ Γ }`. -/
def dualPoly (Γ : Finset (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {u | (∀ i, 0 ≤ u i) ∧ ∀ α ∈ Γ, 1 ≤ α ⬝ᵥ u}

/-- The near-optimal slab `P_η = P ∩ {⟨𝟙,u⟩ ≤ 1/t* + η}`. -/
def dualSlab (Γ : Finset (Fin d → ℝ)) (η : ℝ) : Set (Fin d → ℝ) :=
  {u | u ∈ dualPoly Γ ∧ ones ⬝ᵥ u ≤ (newtonDist Γ)⁻¹ + η}

/-- The rows of `P`: coordinates, then exponents. -/
abbrev Row (Γ : Finset (Fin d → ℝ)) := Fin d ⊕ Γ

/-- Row normals. -/
noncomputable def rowA (Γ : Finset (Fin d → ℝ)) : Row Γ → Fin d → ℝ
  | .inl i => Pi.single i 1
  | .inr α => α.1

/-- Row bounds. -/
def rowB (Γ : Finset (Fin d → ℝ)) : Row Γ → ℝ
  | .inl _ => 0
  | .inr _ => 1

theorem dualPoly_eq_sysSet (Γ : Finset (Fin d → ℝ)) : dualPoly Γ = sysSet (rowA Γ) (rowB Γ) := by
  ext u
  simp only [dualPoly, sysSet, mem_ofPred_eq, Sum.forall, rowA, rowB, single_dotProduct, one_mul,
    Subtype.forall]

/-- The slab rows: `P`'s rows plus `-⟨𝟙,u⟩ ≥ -(1/t* + η)`. -/
noncomputable def slabA (Γ : Finset (Fin d → ℝ)) : Row Γ ⊕ Unit → Fin d → ℝ
  | .inl r => rowA Γ r
  | .inr _ => -ones

noncomputable def slabB (Γ : Finset (Fin d → ℝ)) (η : ℝ) : Row Γ ⊕ Unit → ℝ
  | .inl r => rowB Γ r
  | .inr _ => -((newtonDist Γ)⁻¹ + η)

theorem dualSlab_eq_sysSet (Γ : Finset (Fin d → ℝ)) (η : ℝ) :
    dualSlab Γ η = sysSet (slabA Γ) (slabB Γ η) := by
  ext u
  simp only [dualSlab, dualPoly_eq_sysSet, sysSet, mem_ofPred_eq, Sum.forall, slabA, slabB,
    neg_dotProduct, neg_le_neg_iff]
  simp

/-! ### Basic facts about `t*` -/

theorem newtonDist_le_zero_of_empty : newtonDist (∅ : Finset (Fin d → ℝ)) ≤ 0 := by
  by_cases h : {t | ∃ u, IsNewtonCert (∅ : Finset (Fin d → ℝ)) t u}.Nonempty
  · obtain ⟨t, u, hu⟩ := h
    have : ¬ BddAbove {t | ∃ u, IsNewtonCert (∅ : Finset (Fin d → ℝ)) t u} := by
      rintro ⟨B, hB⟩
      have := hB ⟨u, hu.1, hu.2.1, by simp⟩ (a := B + 1)
      linarith
    rw [newtonDist, Real.sSup_of_not_bddAbove this]
  · rw [not_nonempty_iff_eq_empty] at h
    rw [newtonDist, h, Real.sSup_empty]

theorem nonempty_of_newtonDist_pos {Γ : Finset (Fin d → ℝ)} (hd : 0 < newtonDist Γ) :
    Γ.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  rintro rfl
  exact absurd hd (not_lt.mpr newtonDist_le_zero_of_empty)

theorem bddAbove_cert {Γ : Finset (Fin d → ℝ)} (hne : Γ.Nonempty) :
    BddAbove {t | ∃ u, IsNewtonCert Γ t u} := by
  obtain ⟨α₀, hα₀⟩ := hne
  refine ⟨∑ i, |α₀ i|, fun t ⟨u, hu0, hu1, hut⟩ => (hut α₀ hα₀).trans ?_⟩
  refine Finset.sum_le_sum fun i _ => ?_
  have hui : u i ≤ 1 := by
    rw [← hu1]; exact Finset.single_le_sum (fun j _ => hu0 j) (Finset.mem_univ i)
  calc α₀ i * u i ≤ |α₀ i| * u i := mul_le_mul_of_nonneg_right (le_abs_self _) (hu0 i)
    _ ≤ |α₀ i| * 1 := mul_le_mul_of_nonneg_left hui (abs_nonneg _)
    _ = |α₀ i| := mul_one _

theorem le_newtonDist {Γ : Finset (Fin d → ℝ)} (hne : Γ.Nonempty) {t : ℝ} {u : Fin d → ℝ}
    (hu : IsNewtonCert Γ t u) : t ≤ newtonDist Γ :=
  le_csSup (bddAbove_cert hne) ⟨u, hu⟩

/-- On `P`, `⟨𝟙,u⟩ ≥ 1/t*`. -/
theorem one_dot_ge {Γ : Finset (Fin d → ℝ)} (hd : 0 < newtonDist Γ) {u : Fin d → ℝ}
    (hu : u ∈ dualPoly Γ) : (newtonDist Γ)⁻¹ ≤ ones ⬝ᵥ u := by
  have hne := nonempty_of_newtonDist_pos hd
  obtain ⟨hu0, hu1⟩ := hu
  rw [ones_dotProduct]
  set σ := ∑ i, u i
  have hσ : 0 < σ := by
    rcases (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hu0 i).lt_or_eq with h | h
    · exact h
    · exfalso
      have hz : u = 0 := by
        funext i
        exact le_antisymm ((Finset.single_le_sum (fun j _ => hu0 j) (Finset.mem_univ i)).trans
          h.symm.le) (hu0 i)
      obtain ⟨α₀, hα₀⟩ := hne
      have := hu1 α₀ hα₀
      rw [hz, dotProduct_zero] at this
      linarith
  have hc : IsNewtonCert Γ σ⁻¹ (σ⁻¹ • u) := by
    refine ⟨fun i => mul_nonneg (inv_nonneg.mpr hσ.le) (hu0 i), ?_, fun α hα => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      exact inv_mul_cancel₀ hσ.ne'
    · have h := hu1 α hα
      have : ∑ i, α i * (σ⁻¹ • u) i = σ⁻¹ * (α ⬝ᵥ u) := by
        simp only [Pi.smul_apply, smul_eq_mul, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this]
      exact le_mul_of_one_le_right (inv_nonneg.mpr hσ.le) h
  have := le_newtonDist hne hc
  rw [inv_le_comm₀ hd hσ]; exact this

/-! ### Finitely many vertices, finitely many slide directions -/

/-- Joint kernel triviality of a set of rows. -/
def Triv (Γ : Finset (Fin d → ℝ)) (T : Set (Row Γ)) : Prop :=
  ∀ y : Fin d → ℝ, (∀ r ∈ T, rowA Γ r ⬝ᵥ y = 0) → y = 0

/-- Tight rows of `P` at `v`. -/
def tight (Γ : Finset (Fin d → ℝ)) (v : Fin d → ℝ) : Set (Row Γ) :=
  {r | rowA Γ r ⬝ᵥ v = rowB Γ r}

/-- The vertices of `P`. -/
def vertices (Γ : Finset (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {v | v ∈ dualPoly Γ ∧ Triv Γ (tight Γ v)}

theorem vertices_finite (Γ : Finset (Fin d → ℝ)) : (vertices Γ).Finite := by
  refine Set.Finite.of_finite_image (f := tight Γ) (Set.toFinite _) ?_
  intro v hv w hw hvw
  have := hv.2 (v - w) fun r hr => by
    have hr' : r ∈ tight Γ w := hvw ▸ hr
    rw [dotProduct_sub, hr, hr', sub_self]
  exact sub_eq_zero.mp this

/-- The slide directions. -/
def slides (Γ : Finset (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {z | ones ⬝ᵥ z = 1 ∧ ∀ y : Fin d → ℝ,
    (∀ r, rowA Γ r ⬝ᵥ z = 0 → rowA Γ r ⬝ᵥ y = 0) → ones ⬝ᵥ y = 0 → y = 0}

theorem slides_finite (Γ : Finset (Fin d → ℝ)) : (slides Γ).Finite := by
  refine Set.Finite.of_finite_image (f := fun z => {r | rowA Γ r ⬝ᵥ z = 0}) (Set.toFinite _) ?_
  intro z hz w hw hzw
  have hzw' : ∀ r, rowA Γ r ⬝ᵥ z = 0 ↔ rowA Γ r ⬝ᵥ w = 0 := fun r => by
    have := congrArg (r ∈ ·) hzw
    simpa using this
  have := hz.2 (z - w) (fun r hr => by rw [dotProduct_sub, hr, (hzw' r).mp hr, sub_self])
    (by rw [dotProduct_sub, hz.1, hw.1, sub_self])
  exact sub_eq_zero.mp this

theorem exists_pos_le_of_finite {S : Set ℝ} (hS : S.Finite) (hpos : ∀ x ∈ S, 0 < x) :
    ∃ g : ℝ, 0 < g ∧ ∀ x ∈ S, g ≤ x := by
  by_cases hne : S.Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ := hS.exists_minimal hne
    refine ⟨x₀, hpos x₀ hx₀, fun x hx => ?_⟩
    by_contra h
    push Not at h
    exact absurd (hmin hx h.le) (not_le.mpr h)
  · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩

/-! ### The slab estimate -/

theorem dualSlab_mono (Γ : Finset (Fin d → ℝ)) {η η' : ℝ} (h : η ≤ η') :
    dualSlab Γ η ⊆ dualSlab Γ η' := fun _ hu => ⟨hu.1, hu.2.trans (by linarith)⟩

theorem dualSlab_isBounded (Γ : Finset (Fin d → ℝ)) (η : ℝ) :
    ∀ u ∈ dualSlab Γ η, ‖u‖ ≤ |(newtonDist Γ)⁻¹ + η| := by
  rintro u ⟨⟨hu0, -⟩, hu⟩
  rw [ones_dotProduct] at hu
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun i => ?_
  rw [Real.norm_of_nonneg (hu0 i)]
  exact ((Finset.single_le_sum (fun j _ => hu0 j) (Finset.mem_univ i)).trans hu).trans
    (le_abs_self _)

theorem isCompact_dualSlab (Γ : Finset (Fin d → ℝ)) (η : ℝ) : IsCompact (dualSlab Γ η) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · rw [dualSlab_eq_sysSet]; exact isClosed_sysSet _ _
  · exact (isBounded_iff_forall_norm_le).mpr ⟨_, dualSlab_isBounded Γ η⟩

theorem convex_dualSlab (Γ : Finset (Fin d → ℝ)) (η : ℝ) : Convex ℝ (dualSlab Γ η) := by
  rw [dualSlab_eq_sysSet]; exact convex_sysSet _ _

/-- **Hoffman-type slab bound**: for small `η ≥ 0`, `P_η ⊆ P_0 + closedBall 0 (C η)`. -/
theorem dualSlab_subset {Γ : Finset (Fin d → ℝ)} (hd : 0 < newtonDist Γ) :
    ∃ g : ℝ, 0 < g ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ η, 0 ≤ η → η < g →
      dualSlab Γ η ⊆ dualSlab Γ 0 + closedBall 0 (C * η) := by
  set τ := (newtonDist Γ)⁻¹
  -- the gap above `1/t*` among the vertices
  obtain ⟨g, hg, hgap⟩ := exists_pos_le_of_finite
    (((vertices_finite Γ).inter_of_left {v | τ < ones ⬝ᵥ v}).image fun v => ones ⬝ᵥ v - τ)
    (by rintro _ ⟨v, ⟨-, hv⟩, rfl⟩; exact sub_pos.mpr hv)
  have hgap' : ∀ v ∈ vertices Γ, τ < ones ⬝ᵥ v → g ≤ ones ⬝ᵥ v - τ := fun v hv h =>
    hgap _ ⟨v, ⟨hv, h⟩, rfl⟩
  -- the slide bound
  obtain ⟨C₀, hC₀⟩ := (isBounded_iff_forall_norm_le).mp (slides_finite Γ).isBounded
  refine ⟨g, hg, max C₀ 0, le_max_right _ _, fun η hη hηg => ?_⟩
  have hT_conv : Convex ℝ (dualSlab Γ 0 + closedBall (0 : Fin d → ℝ) (max C₀ 0 * η)) :=
    (convex_dualSlab Γ 0).add (convex_closedBall _ _)
  have hT_closed : IsClosed (dualSlab Γ 0 + closedBall (0 : Fin d → ℝ) (max C₀ 0 * η)) :=
    isClosed_closedBall.add_left_of_isCompact (isCompact_dualSlab Γ 0)
  rw [← closure_convexHull_extremePoints (isCompact_dualSlab Γ η) (convex_dualSlab Γ η)]
  refine closure_minimal (convexHull_min ?_ hT_conv) hT_closed
  intro v hv
  have hv' := hv
  rw [dualSlab_eq_sysSet] at hv'
  have hT : ∀ z : Fin d → ℝ, (∀ r, slabA Γ r ⬝ᵥ v = slabB Γ η r → slabA Γ r ⬝ᵥ z = 0) →
      z = 0 := fun z hz => eq_zero_of_extremePoint _ _ hv' hz
  obtain ⟨hvP, hvτ⟩ := hv.1
  have hv0 : v = v + 0 := (add_zero v).symm
  have hball0 : (0 : Fin d → ℝ) ∈ closedBall 0 (max C₀ 0 * η) :=
    mem_closedBall_self (mul_nonneg (le_max_right _ _) hη)
  -- the restricted kernel condition
  have hTriv_of : (∀ y : Fin d → ℝ, (∀ r ∈ tight Γ v, rowA Γ r ⬝ᵥ y = 0) → ones ⬝ᵥ y = 0 →
      y = 0) := fun y hy h1 => hT y fun r hr => by
    rcases r with r | _
    · exact hy r hr
    · simp only [slabA, neg_dotProduct, h1, neg_zero]
  have hτv := one_dot_ge hd hvP
  -- in `P_0` already?
  by_cases hv0P : ones ⬝ᵥ v ≤ τ
  · rw [hv0]; exact add_mem_add ⟨hvP, by linarith⟩ hball0
  push Not at hv0P
  by_cases hlt : ones ⬝ᵥ v < τ + η
  · -- the cap row is slack, so `v` is a vertex of `P`
    have hvV : v ∈ vertices Γ := by
      refine ⟨hvP, fun y hy => hT y fun r hr => ?_⟩
      rcases r with r | _
      · exact hy r hr
      · exfalso; simp only [slabA, slabB, neg_dotProduct, neg_inj] at hr; linarith
    have := hgap' v hvV hv0P
    linarith
  have heq : ones ⬝ᵥ v = τ + η := le_antisymm hvτ (not_lt.mp hlt)
  by_cases hTr : Triv Γ (tight Γ v)
  · have := hgap' v ⟨hvP, hTr⟩ hv0P
    linarith
  -- a slide direction
  simp only [Triv, not_forall] at hTr
  obtain ⟨z₀, hz₀, hz₀ne⟩ := hTr
  have h1z₀ : ones ⬝ᵥ z₀ ≠ 0 := fun h => hz₀ne (hTriv_of z₀ hz₀ h)
  set z := (ones ⬝ᵥ z₀)⁻¹ • z₀
  have hz1 : ones ⬝ᵥ z = 1 := by rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ h1z₀]
  have hzT : ∀ r ∈ tight Γ v, rowA Γ r ⬝ᵥ z = 0 := fun r hr => by
    rw [dotProduct_smul, hz₀ r hr, smul_zero]
  have hkey : ∀ y : Fin d → ℝ, (∀ r ∈ tight Γ v, rowA Γ r ⬝ᵥ y = 0) →
      y = (ones ⬝ᵥ y) • z := fun y hy => by
    have := hTriv_of (y - (ones ⬝ᵥ y) • z)
      (fun r hr => by rw [dotProduct_sub, dotProduct_smul, hy r hr, hzT r hr]; simp)
      (by rw [dotProduct_sub, dotProduct_smul, hz1]; simp)
    exact sub_eq_zero.mp this
  have hzS : z ∈ slides Γ := ⟨hz1, fun y hy hy1 => by
    rw [hkey y fun r hr => hy r (hzT r hr), hy1, zero_smul]⟩
  have hzC : ‖z‖ ≤ max C₀ 0 := (hC₀ z hzS).trans (le_max_left _ _)
  -- rows along which `v - λ z` decreases
  set D := Finset.univ.filter fun r : Row Γ => 0 < rowA Γ r ⬝ᵥ z
  have hP : ∀ lam : ℝ, 0 ≤ lam → (∀ r ∈ D, lam * (rowA Γ r ⬝ᵥ z) ≤ rowA Γ r ⬝ᵥ v - rowB Γ r) →
      v - lam • z ∈ dualPoly Γ := fun lam hlam hD => by
    rw [dualPoly_eq_sysSet]
    intro r
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    by_cases hr : r ∈ D
    · linarith [hD r hr]
    · have : rowA Γ r ⬝ᵥ z ≤ 0 := by simpa [D] using hr
      have := (dualPoly_eq_sysSet Γ ▸ hvP) r
      nlinarith
  by_cases hall : ∀ r ∈ D, η * (rowA Γ r ⬝ᵥ z) ≤ rowA Γ r ⬝ᵥ v - rowB Γ r
  · -- slide all the way down to `P_0`
    have hv₀ : v - η • z ∈ dualSlab Γ 0 := by
      refine ⟨hP η hη hall, ?_⟩
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hz1, heq]; linarith
    have : v = (v - η • z) + η • z := by abel
    rw [this]
    refine add_mem_add hv₀ ?_
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hη, mul_comm]
    exact mul_le_mul_of_nonneg_right hzC hη
  · -- a row blocks the slide first: a vertex of `P` strictly inside the gap
    exfalso
    push Not at hall
    obtain ⟨r₀, hr₀D, hr₀⟩ := hall
    have hDne : D.Nonempty := ⟨r₀, hr₀D⟩
    set f : Row Γ → ℝ := fun r => (rowA Γ r ⬝ᵥ v - rowB Γ r) / (rowA Γ r ⬝ᵥ z)
    obtain ⟨rs, hrsD, hrs⟩ := D.exists_min_image f hDne
    have hpos : ∀ r ∈ D, 0 < rowA Γ r ⬝ᵥ z := fun r hr => by simpa [D] using hr
    have hslack : ∀ r, 0 ≤ rowA Γ r ⬝ᵥ v - rowB Γ r := fun r =>
      sub_nonneg.mpr ((dualPoly_eq_sysSet Γ ▸ hvP) r)
    set lam := f rs
    have hlam0 : 0 ≤ lam := div_nonneg (hslack rs) (hpos rs hrsD).le
    have hlamη : lam < η := by
      have h1 : f r₀ < η := by
        rw [div_lt_iff₀ (hpos r₀ hr₀D)]; linarith
      exact lt_of_le_of_lt (hrs r₀ hr₀D) h1
    have hw : v - lam • z ∈ dualPoly Γ := hP lam hlam0 fun r hr => by
      have := hrs r hr
      rwa [le_div_iff₀ (hpos r hr)] at this
    have hwV : v - lam • z ∈ vertices Γ := by
      refine ⟨hw, fun y hy => ?_⟩
      have hyv : ∀ r ∈ tight Γ v, rowA Γ r ⬝ᵥ y = 0 := fun r hr => hy r (by
        simp only [tight, mem_ofPred_eq, dotProduct_sub, dotProduct_smul, hzT r hr, smul_zero,
          sub_zero]; exact hr)
      have hys : rowA Γ rs ⬝ᵥ y = 0 := hy rs (by
        simp only [tight, mem_ofPred_eq, dotProduct_sub, dotProduct_smul, smul_eq_mul, lam, f]
        field_simp [(hpos rs hrsD).ne']
        ring)
      have hyz := hkey y hyv
      rw [hyz, dotProduct_smul, smul_eq_mul] at hys
      rcases mul_eq_zero.mp hys with h | h
      · rw [hyz, h, zero_smul]
      · exact absurd h (hpos rs hrsD).ne'
    have hwτ : ones ⬝ᵥ (v - lam • z) = τ + η - lam := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hz1, heq, mul_one]
    have := hgap' _ hwV (by rw [hwτ]; linarith)
    rw [hwτ] at this
    linarith

end SLT.Newton
