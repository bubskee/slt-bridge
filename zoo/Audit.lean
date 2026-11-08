import Zoo

/-! Axiom audit for the zoo. Run: `lake env lean Audit.lean`. -/

#print axioms SLT.Zoo.ResidualNetwork.hasLaplaceOrder_iff
#print axioms SLT.Zoo.ResidualNetwork.prior
#print axioms SLT.Zoo.ResidualNetwork.global_pair
#print axioms SLT.Zoo.ResidualNetwork.global_pair_unique
#print axioms SLT.Zoo.ResidualNetwork.residualNetwork_learningPair
#print axioms SLT.Zoo.ResidualNetwork.local_pair
#print axioms SLT.Zoo.ResidualNetwork.cubic_depth6_three_active
#print axioms SLT.Zoo.ResidualNetwork.cubic_depth5_local_split13
#print axioms SLT.Zoo.ResidualNetwork.cubic_depth5_local_split22
#print axioms SLT.Zoo.VectorShear.ofVector
#print axioms SLT.Zoo.VectorShear.toVector
#print axioms SLT.Zoo.VectorShear.position_one_pair
#print axioms SLT.Zoo.VectorShear.position_one_unique
#print axioms SLT.Zoo.VectorShear.mainTheorem_shear_core
#print axioms SLT.Zoo.VectorShear.position_one_ne_position
#print axioms SLT.Zoo.VectorShear.mainTheorem_shear_gaussian_core

-- the source theorems, re-checked here
#print axioms ResidualSLT.unified_residual_network_certificate
#print axioms VectorSLT.ZN1_two_sided_moments
#print axioms VectorSLT.mainTheorem_shear
#print axioms VectorSLT.mainTheorem_shear_gaussian

/-! Brief 01, stage L3 (LLC corollaries). -/
#print axioms SLT.Zoo.residualNetwork_llc_log_average
#print axioms SLT.Zoo.residualNetwork_llc
#print axioms SLT.Zoo.cubic_depth6_three_active_llc
#print axioms SLT.Zoo.measurable_popLossA
#print axioms SLT.Zoo.Zpos_eq_Z
#print axioms SLT.Zoo.isFiniteMeasure_posPrior
#print axioms SLT.Zoo.position_one_llc
#print axioms SLT.Zoo.mainTheorem_shear_llc

/-! Brief 02 (cleanliness pass). -/
#print axioms SLT.Zoo.posPrior

/-! Brief 03, T1 guardrail: Theorem M through the elementary template. -/
#print axioms SLT.Zoo.TemplateM.chartD
#print axioms SLT.Zoo.TemplateM.rowWeight
#print axioms SLT.Zoo.TemplateM.angW
#print axioms SLT.Zoo.TemplateM.pivotRegion_eq
#print axioms SLT.Zoo.TemplateM.e2_symm_apply
#print axioms SLT.Zoo.TemplateM.angW_int
#print axioms SLT.Zoo.TemplateM.Bcone
#print axioms SLT.Zoo.TemplateM.rowWeight_minLogBound
#print axioms SLT.Zoo.TemplateM.CrowT
#print axioms SLT.Zoo.TemplateM.pivotRow_template
#print axioms SLT.Zoo.TemplateM.rowBound_template
#print axioms SLT.Zoo.TemplateM.rowBound_M6_template
#print axioms SLT.Zoo.TemplateM.BrowT
#print axioms SLT.Zoo.TemplateM.BrowT_ne_top
#print axioms SLT.Zoo.TemplateM.J_bound_template
#print axioms SLT.Zoo.TemplateM.UM_c_template
#print axioms SLT.Zoo.TemplateM.Fbox
#print axioms SLT.Zoo.TemplateM.Fbox_le
#print axioms SLT.Zoo.TemplateM.CrowT_nonneg
#print axioms SLT.Zoo.TemplateM.Fbox_laplaceUpper
#print axioms SLT.Zoo.TemplateM.Zpos_le_Fbox
#print axioms SLT.Zoo.TemplateM.Zpos_one_laplaceUpper
#print axioms SLT.Zoo.TemplateM.ZN1_two_sided_template
#print axioms SLT.Zoo.TemplateM.position_one_pair_template
-- the source lemmas the re-derivation uses as hypothesis dischargers, re-checked here
#print axioms VectorSLT.lemmaM4
#print axioms VectorSLT.m3Int_Echart
#print axioms VectorSLT.Gdown
#print axioms VectorSLT.UM_inner
#print axioms VectorSLT.Zpos_one_lower
