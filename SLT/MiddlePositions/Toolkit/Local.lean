/-
Copyright (c) 2026 Bobby Faber. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import SLT.MiddlePositions.Defs
public import SLT.PositionFour.Upstream.Local

/-!
# Local integrability of `F` (note §2, Lemma "Weighted two-cube measure bound", second half)

`locallyIntegrableF`: the interface statement `LocallyIntegrableF`. Both summands of `F` are
bounded on a ball by a constant times `|𝔇|^{-t}` with `t = 4/3` or `t = 11/8`, which is integrable
on balls by `SLT.PositionFour.lintegral_closedBall_discDensity_lt_top` (the cone chart of
`SLT/PositionFour/Upstream/Local.lean`, at a general exponent `1 < t ≤ 3/2`).
-/

@[expose] public section

namespace SLT.MiddlePositions

open MeasureTheory Set Metric SLT.PositionFour
open scoped ENNReal

/-! ### Local integrability of `F` -/

/-- `F = |𝔇|^{-4/3} + ‖P‖^{1/4} |𝔇|^{-11/8}`. -/
theorem F_eq (P : Cubic) :
    F P = twoCubeDensity P + ENNReal.ofReal (‖P‖ ^ (1 / 4 : ℝ)) * discDensity (11 / 8) P := rfl

/-- **Interface 2, proved.** `F` is integrable on every closed ball. -/
theorem locallyIntegrableF : LocallyIntegrableF := by
  intro r
  set r' := max r 0
  have hb : ∀ P ∈ closedBall (0 : Cubic) r,
      ENNReal.ofReal (‖P‖ ^ (1 / 4 : ℝ)) * discDensity (11 / 8) P ≤
        ENNReal.ofReal (r' ^ (1 / 4 : ℝ)) * discDensity (11 / 8) P := by
    intro P hP
    have hPr : ‖P‖ ≤ r' := (mem_closedBall_zero_iff.mp hP).trans (le_max_left _ _)
    gcongr
  simp_rw [F_eq]
  rw [lintegral_add_left measurable_twoCubeDensity]
  refine ENNReal.add_lt_top.mpr ⟨lintegral_closedBall_twoCubeDensity_lt_top r, ?_⟩
  calc ∫⁻ P in closedBall (0 : Cubic) r,
        ENNReal.ofReal (‖P‖ ^ (1 / 4 : ℝ)) * discDensity (11 / 8) P
      ≤ ∫⁻ P in closedBall (0 : Cubic) r,
          ENNReal.ofReal (r' ^ (1 / 4 : ℝ)) * discDensity (11 / 8) P :=
        setLIntegral_mono (by fun_prop) hb
    _ = ENNReal.ofReal (r' ^ (1 / 4 : ℝ)) *
          ∫⁻ P in closedBall (0 : Cubic) r, discDensity (11 / 8) P :=
        lintegral_const_mul _ (measurable_discDensity _)
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lintegral_closedBall_discDensity_lt_top (by norm_num) (by norm_num) r)

end SLT.MiddlePositions
