import SLT.MiddlePositions.Two

/-! Axiom audit for position two of the middle positions (`SLT/MiddlePositions/Two.lean` and
`SLT/MiddlePositions/Two/`): one line per public declaration of those modules (77). The shared
`SLT/MiddlePositions/Defs.lean` is not listed here. Run:
`lake env lean SLT/MiddlePositions/AuditTwo.lean`. Every line should report only
`propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms SLT.MiddlePositions.Two.Bsuf
#print axioms SLT.MiddlePositions.Two.Cphi
#print axioms SLT.MiddlePositions.Two.Cphi_lt_top
#print axioms SLT.MiddlePositions.Two.F_le
#print axioms SLT.MiddlePositions.Two.G
#print axioms SLT.MiddlePositions.Two.L
#print axioms SLT.MiddlePositions.Two.L_le
#print axioms SLT.MiddlePositions.Two.Lc
#print axioms SLT.MiddlePositions.Two.Lc_pos
#print axioms SLT.MiddlePositions.Two.Msuf
#print axioms SLT.MiddlePositions.Two.Mz
#print axioms SLT.MiddlePositions.Two.N2b
#print axioms SLT.MiddlePositions.Two.V
#print axioms SLT.MiddlePositions.Two.V_le
#print axioms SLT.MiddlePositions.Two.box
#print axioms SLT.MiddlePositions.Two.continuous_R2
#print axioms SLT.MiddlePositions.Two.coordsEquiv
#print axioms SLT.MiddlePositions.Two.disc_coords
#print axioms SLT.MiddlePositions.Two.enorm_inv_rpow_ne_zero
#print axioms SLT.MiddlePositions.Two.enorm_mul_inv_rpow'
#print axioms SLT.MiddlePositions.Two.enorm_zero_inv_rpow
#print axioms SLT.MiddlePositions.Two.fullPlaneQuadratic_mono
#print axioms SLT.MiddlePositions.Two.indicator_one_mul_eq
#print axioms SLT.MiddlePositions.Two.indicator_one_ne_top
#print axioms SLT.MiddlePositions.Two.lintegral_F_coords_le
#print axioms SLT.MiddlePositions.Two.lintegral_G_le
#print axioms SLT.MiddlePositions.Two.lintegral_W2_box_le
#print axioms SLT.MiddlePositions.Two.lintegral_W2_le
#print axioms SLT.MiddlePositions.Two.lintegral_coords
#print axioms SLT.MiddlePositions.Two.lintegral_inv_quadratic_le
#print axioms SLT.MiddlePositions.Two.lintegral_max_one_rpow_neg_lt_top
#print axioms SLT.MiddlePositions.Two.lintegral_pre1_le
#print axioms SLT.MiddlePositions.Two.lintegral_pre1_lt_top
#print axioms SLT.MiddlePositions.Two.lintegral_pre_lt_top
#print axioms SLT.MiddlePositions.Two.lintegral_rpow_mul_inv_quadratic_le
#print axioms SLT.MiddlePositions.Two.max_rpow_le_add
#print axioms SLT.MiddlePositions.Two.measurableSet_box
#print axioms SLT.MiddlePositions.Two.measurableSet_preSet
#print axioms SLT.MiddlePositions.Two.measurable_Bsuf
#print axioms SLT.MiddlePositions.Two.measurable_Bsuf_right
#print axioms SLT.MiddlePositions.Two.measurable_F
#print axioms SLT.MiddlePositions.Two.measurable_W2
#print axioms SLT.MiddlePositions.Two.measurable_box_indicator
#print axioms SLT.MiddlePositions.Two.measurable_pre
#print axioms SLT.MiddlePositions.Two.measurable_pre1
#print axioms SLT.MiddlePositions.Two.measurable_twoCube'
#print axioms SLT.MiddlePositions.Two.measurePreserving_coordsEquiv
#print axioms SLT.MiddlePositions.Two.norm_coords_le
#print axioms SLT.MiddlePositions.Two.norm_lt_one_of_cube
#print axioms SLT.MiddlePositions.Two.norm_rpow_le_W2
#print axioms SLT.MiddlePositions.Two.norm_rpow_le_weight
#print axioms SLT.MiddlePositions.Two.ofCoords
#print axioms SLT.MiddlePositions.Two.ofReal_one_add_rpow_mul_le
#print axioms SLT.MiddlePositions.Two.one_le_W2
#print axioms SLT.MiddlePositions.Two.pre
#print axioms SLT.MiddlePositions.Two.pre1
#print axioms SLT.MiddlePositions.Two.preSet
#print axioms SLT.MiddlePositions.Two.pre_comm
#print axioms SLT.MiddlePositions.Two.quadW
#print axioms SLT.MiddlePositions.Two.quadW_nonneg
#print axioms SLT.MiddlePositions.Two.rowSet
#print axioms SLT.MiddlePositions.Two.rpow_mul_L_le
#print axioms SLT.MiddlePositions.Two.rpow_mul_rpow_eq
#print axioms SLT.MiddlePositions.Two.setLIntegral_G_le
#print axioms SLT.MiddlePositions.Two.setLIntegral_N2b_le
#print axioms SLT.MiddlePositions.Two.setLIntegral_ball_inv_rpow_le
#print axioms SLT.MiddlePositions.Two.setLIntegral_ball_inv_rpow_le_three_pi
#print axioms SLT.MiddlePositions.Two.setLIntegral_box_F_le
#print axioms SLT.MiddlePositions.Two.sq_rpow_mul_rpow_eq
#print axioms SLT.MiddlePositions.Two.sublevelTwo
#print axioms SLT.MiddlePositions.Two.sublevel_indicator_le
#print axioms SLT.MiddlePositions.Two.sublevel_two_le
#print axioms SLT.MiddlePositions.Two.unweighted_term_le
#print axioms SLT.MiddlePositions.Two.volume_ball_one
#print axioms SLT.MiddlePositions.Two.volume_coupling_le
#print axioms SLT.MiddlePositions.Two.volume_prefix_le
#print axioms SLT.MiddlePositions.Two.weighted_term_le
