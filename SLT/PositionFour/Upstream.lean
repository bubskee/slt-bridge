/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.PositionFour.Upstream.Algebra
public import SLT.PositionFour.Upstream.Sylvester
public import SLT.PositionFour.Upstream.Area
public import SLT.PositionFour.Upstream.Coords
public import SLT.PositionFour.Upstream.Planar
public import SLT.PositionFour.Upstream.Reference
public import SLT.PositionFour.Upstream.RefFibre
public import SLT.PositionFour.Upstream.TwoCube
public import SLT.PositionFour.Upstream.Density
public import SLT.PositionFour.Upstream.Cusp
public import SLT.PositionFour.Upstream.Local

/-!
# The upstream half of the complex position-four threshold (note §1)

Root import for the upstream modules. The two interface statements of `Defs.lean`, for every
`0 ≤ β < 2`:

* `upstream_densityBound`: `∃ C, DensityBound β C` (the note's equation (2));
* `upstream_locallyFiniteRow`: `LocallyFiniteRow β`.

No named hypothesis remains: the two-cube pushforward (step 3) is proved as `twoCubeBound`.

Where each step of the note's §1 lives:

* reference integral `∬ w_β(x) w_β(y) |x - y|^{-2/3} < ∞`: `lintegral_refBilinear_lt_top`;
* the algebra of `verify_algebra.py`: `disc_twoCube`, `hess_twoCube`, `disc_refCubic_sub_cube`,
  `root_substitution`, `disc_cubicAct`, `hess_cubicAct`;
* Sylvester (existence, uniqueness, `18` preimages): `exists_twoCube_eq`, `twoCube_eq_twoCube`,
  `exists_finset_twoCube_fibre`;
* two-cube density `≤ (2/9) |𝔇|^{-4/3}`: `twoCubeBound`;
* `ρ_β(P*) < ∞`: `refFibre_lt_top`;
* `‖g‖ ≲ ‖P‖^{1/3} + ‖H‖^{1/2} |𝔇|^{-1/6}`: `norm_twoCube_cases`, `two_norm_rpow_le`;
* transport and equation (2): `rhoTilde_le_of_twoCube`, `rhoTilde_le_densityBound`,
  `densityBound_holds`;
* local finiteness: `lintegral_closedBall_twoCubeDensity_lt_top`, `locallyFiniteRow`.
-/

@[expose] public section

namespace SLT.PositionFour

/-- **Interface, part 1.** For `0 ≤ β < 2`, the weighted row pushforward is dominated by a
constant times the note's bounding density (2). -/
theorem upstream_densityBound (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 2) : ∃ C, DensityBound β C :=
  exists_densityBound hβ0 hβ

/-- **Interface, part 2.** For `0 ≤ β < 2`, the weighted row pushforward is finite on closed
balls. -/
theorem upstream_locallyFiniteRow (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 2) : LocallyFiniteRow β :=
  locallyFiniteRow hβ0 hβ

end SLT.PositionFour
