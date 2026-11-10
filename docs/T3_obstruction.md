# T3 obstruction note: leading map + remainder (brief 03, overnight run 04)

**Shipped.** The nondegenerate case is proved. `SLT.Template.hasLaplacePair_of_leading` and
`exists_hasLaplacePair_of_leading` give the pair `(D/(2d), 1)` for `G = G₀ + R` under these hypotheses:
- `G₀` is continuous and homogeneous of degree `2d`;
- `G₀` is positive away from `0`, so the leading map has an isolated zero;
- the remainder satisfies `|R| ≤ C ‖w‖^{2d+1}`.

All of these are checkable inequalities. The guardrail is met:
`SLT.Zoo.TemplateLeading.positive_homogeneous_laplace_order_template` re-derives residual-slt's
`positive_homogeneous_laplace_order` (on `Fin D → ℝ` with Lebesgue measure) as the zero-remainder case.

**Not shipped: the degenerate case, and why.**

1. **Where it fits and where it doesn't.** The remainder control does fit a weight filtration, but only
   when the leading part is nondegenerate on the shell. Then `G(rξ)/r^{2d} ≥ c - C r`, and the angular margin
   follows for every `s` (`angularMargin_of_leading`).

   When the leading map `R` has nonzero zeros on the shell, the angular factor
   `H(r, ξ) = ‖R(ξ) + r·(…)‖²` vanishes near those zeros. A higher-weight remainder can then change the
   integrability exponent of `H(r,·)^{-s}`, in either direction. Bounding `∫ H(r,·)^{-s}` uniformly in `r`
   is exactly Phong–Sturm stability: a semicontinuity of complex singularity exponents under holomorphic
   deformation. It has no elementary proof and is not in Mathlib or hironaka. So in the degenerate case the
   named hypothesis stays `AngularMargin` (T2).

2. **The shear network's inactive maps and the read/write blocks are degenerate.** Cubic-chaos's leading
   maps `R_j` vanish on the aligned and zero-row families (Theorem K §1). A single read/write block
   `c = u v³` at `(0,0)` has leading part `(u v³)²`, which vanishes on both axes. So T3's nondegenerate form
   does **not** cover rw-bridge's `u (vᵀx)³` blocks directly.

3. **What does cover rw-bridge's blocks today: the core's Newton theorem (N2).** Suppose the local loss is
   two-sided comparable to a monomial sum, `K ≍ Σ_α |w|^α`. Then `SLT.Newton.newtonTwoSided` gives
   `(1/t*, dim O + 1)`.
   - Example: one block `c = u v³` gives `Γ = {(2,6)}`, so `t* = 6`, `λ = 1/6`, `m = 1`. That matches
     Lemma R0.1's `|c|^{-2/3}` density reading (each `c` contributes `λ = 1/6`, as for raw `w³`).
   - What a new architecture has to check is the comparison `c Σ|w|^α ≤ K ≤ C Σ|w|^α` on a box. For a
     factored scalar model that comparison is elementary. The comparison is the honest "remainder control"
     for monomial-type leading maps.
4. **Missing piece: anisotropic weights.** T3 uses isotropic scaling `w ↦ r w`. A quasi-homogeneous version
   (weights `q_i`, scaling `w_i ↦ r^{q_i} w_i`, `λ = Σq_i/(2d)`) would cover nondegenerate quasi-homogeneous
   leading maps such as `(u, v³)` with weights `(3, 1)`. The proof is the same: the rescaling lemma becomes a
   product of 1-D rescalings with Jacobian `r^{Σq_i}`. It is not built because it has no consumer yet. It
   would be about 150 lines.

**Also costed, not built: constructing `PositionMargin`'s (K3) data (the forum's target).** The goal is to
build `Ψ` and the comparison from a leading map with an invertible active block, leaving `AngularMargin` as
the only named hypothesis in the shear table. That needs three pieces:
- the inverse function theorem for `(α, w) ↦ (U(α, w), w)` near the base point, with
  `∂U/∂α = 3 · I` (Mathlib: `HasStrictFDerivAt.toOpenPartialHomeomorph`);
- a nonlinear change of variables with Jacobian bounds on the image (Mathlib:
  `lintegral_image_eq_lintegral_abs_det_fderiv_mul`), giving the `∫ f∘Ψ · ρ ≤ J ∫ f` field;
- the comparison `K ≍ |u|² + ‖g(0,w)‖²` from `g(u,w) - g(0,w) = O(|u|)` and the Gram bound. The Gram bound
  exists in vector-slt-lean as `Gdown`, but only for position one's coefficients.

Estimate: 600–1000 lines per position, mostly the network's explicit coefficient polynomials at positions
2–4 (vector-slt-lean has them only for position one, through the M2 coordinates). It is recorded in
the project plan (kept outside this repository) and was stopped there, as the forum allowed.
