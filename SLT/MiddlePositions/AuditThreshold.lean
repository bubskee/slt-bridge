import SLT.MiddlePositions.Threshold
import SLT.PositionFour.Threshold

/-! Axiom audit for the joined, unconditional complex margins at positions two, three and four.
Run: `lake env lean SLT/MiddlePositions/AuditThreshold.lean`. The component audits are
`AuditToolkit.lean`, `AuditTwo.lean`, `AuditThree.lean` and those of `SLT/PositionFour/`. -/

#print axioms SLT.MiddlePositions.sublevelTwo
#print axioms SLT.MiddlePositions.sublevelThree
#print axioms SLT.MiddlePositions.shellTwo_lintegral_lt_top
#print axioms SLT.MiddlePositions.shellThree_lintegral_lt_top
#print axioms SLT.PositionFour.volume_sublevel_lt_top
#print axioms SLT.PositionFour.shell_lintegral_lt_top
