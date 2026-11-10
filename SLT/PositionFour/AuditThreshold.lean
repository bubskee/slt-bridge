import SLT.PositionFour.Threshold

/-! Axiom audit for the joined, unconditional position-four statements of
`SLT.PositionFour.Threshold`. Run: `lake env lean SLT/PositionFour/AuditThreshold.lean`. The two
halves have their own audits (`AuditUpstream.lean`, `AuditDownstream.lean`). -/

#print axioms SLT.PositionFour.interface
#print axioms SLT.PositionFour.sublevel_weighted_lt_top
#print axioms SLT.PositionFour.volume_sublevel_lt_top
#print axioms SLT.PositionFour.shell_lintegral_lt_top
#print axioms SLT.PositionFour.integrableOn_shell
