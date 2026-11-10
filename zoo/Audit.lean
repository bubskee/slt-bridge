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

/-! Brief 03, T2 guardrail: `ThmK`/`ThmN` as instances of the margin template. -/
#print axioms SLT.Zoo.TemplateMargin.PositionMargin
#print axioms SLT.Zoo.TemplateMargin.Zpos_le_marginModel
#print axioms SLT.Zoo.TemplateMargin.Zpos_upper_of_margin
#print axioms SLT.Zoo.TemplateMargin.thmN_of_margin
#print axioms SLT.Zoo.TemplateMargin.thmKUpper_of_margin
#print axioms SLT.Zoo.TemplateMargin.thmK_of_margin
#print axioms SLT.Zoo.TemplateMargin.mainTheorem_shear_of_margin
#print axioms VectorSLT.Zpos_lower_N4

/-! Brief 03, T3 guardrail: positive homogeneous losses through the leading-map template. -/
#print axioms SLT.Zoo.TemplateLeading.hasLaplacePair_of_homogeneous_add_remainder
#print axioms SLT.Zoo.TemplateLeading.ofReal_ball_integral
#print axioms SLT.Zoo.TemplateLeading.one_le_of_nontrivial
#print axioms SLT.Zoo.TemplateLeading.positive_homogeneous_laplace_order_template
-- the source theorem, re-checked here
#print axioms ResidualSLT.positive_homogeneous_laplace_order

/-! Brief 03, T4: one factored read/write block `c = u v³`. -/
#print axioms SLT.Zoo.ReadWrite.Z_translate
#print axioms SLT.Zoo.ReadWrite.crossing_readDead_ne_writeDead
#print axioms SLT.Zoo.ReadWrite.measurable_oneBlockLoss
#print axioms SLT.Zoo.ReadWrite.monoSum_crossing
#print axioms SLT.Zoo.ReadWrite.monoSum_readDead
#print axioms SLT.Zoo.ReadWrite.monoSum_writeDead
#print axioms SLT.Zoo.ReadWrite.newtonDist_crossing
#print axioms SLT.Zoo.ReadWrite.newtonDist_readDead
#print axioms SLT.Zoo.ReadWrite.newtonMult_eq_one_of_singleton
#print axioms SLT.Zoo.ReadWrite.oneBlockLoss
#print axioms SLT.Zoo.ReadWrite.oneBlock_crossing_pair
#print axioms SLT.Zoo.ReadWrite.oneBlock_readDead_pair
#print axioms SLT.Zoo.ReadWrite.oneBlock_writeDead_pair
#print axioms SLT.Zoo.ReadWrite.optWeights_crossing
#print axioms SLT.Zoo.ReadWrite.optWeights_readDead
#print axioms SLT.Zoo.ReadWrite.withDensity_one_box

/-! Brief 04, T5 (MLP arrangement ideals). -/
#print axioms SLT.Zoo.MLP.cplLoss
#print axioms SLT.Zoo.MLP.cplLoss_generic_pair
#print axioms SLT.Zoo.MLP.cplLoss_slice_pair
#print axioms SLT.Zoo.MLP.dupDup_pair
#print axioms SLT.Zoo.MLP.dupLoss
#print axioms SLT.Zoo.MLP.dupLoss_pair
#print axioms SLT.Zoo.MLP.isNewtonCert_powCert
#print axioms SLT.Zoo.MLP.m1_m4_pair
#print axioms SLT.Zoo.MLP.m2_pair
#print axioms SLT.Zoo.MLP.m3'_pair
#print axioms SLT.Zoo.MLP.m3_pair
#print axioms SLT.Zoo.MLP.m4_ne_m3'
#print axioms SLT.Zoo.MLP.measurable_regLoss
#print axioms SLT.Zoo.MLP.measurable_spareLoss
#print axioms SLT.Zoo.MLP.monoSum_M3
#print axioms SLT.Zoo.MLP.monoSum_bothIn
#print axioms SLT.Zoo.MLP.monoSum_bothOut
#print axioms SLT.Zoo.MLP.monoSum_inBoth
#print axioms SLT.Zoo.MLP.monoSum_outBoth
#print axioms SLT.Zoo.MLP.monoSum_powΓ
#print axioms SLT.Zoo.MLP.newtonDist_M3
#print axioms SLT.Zoo.MLP.newtonDist_bothIn
#print axioms SLT.Zoo.MLP.newtonDist_bothOut
#print axioms SLT.Zoo.MLP.newtonDist_inBoth
#print axioms SLT.Zoo.MLP.newtonDist_outBoth
#print axioms SLT.Zoo.MLP.newtonDist_powΓ
#print axioms SLT.Zoo.MLP.newtonMult_M3
#print axioms SLT.Zoo.MLP.newtonMult_bothOut
#print axioms SLT.Zoo.MLP.newtonMult_eq_two
#print axioms SLT.Zoo.MLP.newtonMult_inBoth
#print axioms SLT.Zoo.MLP.optWeights_M3
#print axioms SLT.Zoo.MLP.optWeights_bothIn
#print axioms SLT.Zoo.MLP.optWeights_bothOut
#print axioms SLT.Zoo.MLP.optWeights_inBoth
#print axioms SLT.Zoo.MLP.optWeights_outBoth
#print axioms SLT.Zoo.MLP.optWeights_powΓ
#print axioms SLT.Zoo.MLP.outIn_ne_inOut
#print axioms SLT.Zoo.MLP.pair_of_powΓ
#print axioms SLT.Zoo.MLP.pair_of_Γ
#print axioms SLT.Zoo.MLP.powCert
#print axioms SLT.Zoo.MLP.powΓ
#print axioms SLT.Zoo.MLP.regLoss
#print axioms SLT.Zoo.MLP.regLoss_pair
#print axioms SLT.Zoo.MLP.regPlus
#print axioms SLT.Zoo.MLP.regPrior
#print axioms SLT.Zoo.MLP.regular_add_pair
#print axioms SLT.Zoo.MLP.s2pLoss
#print axioms SLT.Zoo.MLP.s2pPrior
#print axioms SLT.Zoo.MLP.s2p_bothIn
#print axioms SLT.Zoo.MLP.s2p_bothOut
#print axioms SLT.Zoo.MLP.s2p_inBoth
#print axioms SLT.Zoo.MLP.s2p_inOut
#print axioms SLT.Zoo.MLP.s2p_outBoth
#print axioms SLT.Zoo.MLP.s2p_outIn
#print axioms SLT.Zoo.MLP.spareLoss
#print axioms SLT.Zoo.MLP.spare_bothIn_pair
#print axioms SLT.Zoo.MLP.spare_bothOut_pair
#print axioms SLT.Zoo.MLP.spare_inBoth_pair
#print axioms SLT.Zoo.MLP.spare_inOut_pair
#print axioms SLT.Zoo.MLP.spare_outBoth_pair
#print axioms SLT.Zoo.MLP.spare_outIn_pair
#print axioms SLT.Zoo.MLP.sqIdealLoss
#print axioms SLT.Zoo.MLP.sqIdealLoss_pair
#print axioms SLT.Zoo.MLP.ΓM3
#print axioms SLT.Zoo.MLP.ΓbothIn
#print axioms SLT.Zoo.MLP.ΓbothOut
#print axioms SLT.Zoo.MLP.ΓinBoth
#print axioms SLT.Zoo.MLP.ΓoutBoth
#print axioms SLT.Zoo.MLP.convex_optWeights
#print axioms SLT.Zoo.MLP.ΓbothBoth
#print axioms SLT.Zoo.MLP.newtonDist_bothBoth
#print axioms SLT.Zoo.MLP.bothBothVertex
#print axioms SLT.Zoo.MLP.optWeights_bothBoth
#print axioms SLT.Zoo.MLP.affineIndependent_bothBothVertex
#print axioms SLT.Zoo.MLP.newtonMult_bothBoth
#print axioms SLT.Zoo.MLP.monoSum_bothBoth
#print axioms SLT.Zoo.MLP.spare_bothBoth_pair
#print axioms SLT.Zoo.MLP.s2p_bothBoth

/-! R0.2 certificate, J(1,1) (2026-11-08). -/
#print axioms SLT.Zoo.MixedGroup.HasLaplacePair.squeeze
#print axioms SLT.Zoo.MixedGroup.mixedLoss
#print axioms SLT.Zoo.MixedGroup.shearLoss
#print axioms SLT.Zoo.MixedGroup.shear
#print axioms SLT.Zoo.MixedGroup.mixedLoss_shear
#print axioms SLT.Zoo.MixedGroup.measurable_shearLoss
#print axioms SLT.Zoo.MixedGroup.measurable_mixedLoss
#print axioms SLT.Zoo.MixedGroup.shearEquiv
#print axioms SLT.Zoo.MixedGroup.measurePreserving_shear
#print axioms SLT.Zoo.MixedGroup.Z_mixed_eq_shear
#print axioms SLT.Zoo.MixedGroup.box_half_subset
#print axioms SLT.Zoo.MixedGroup.preimage_subset_box_two
#print axioms SLT.Zoo.MixedGroup.shearLoss_pair
#print axioms SLT.Zoo.MixedGroup.mixedGroup_pair
#print axioms SLT.Zoo.MixedGroup.mixedGroup_pair_formula

/-! The complex leading maps are the network's (`Zoo/LeadingMaps.lean`). -/
#print axioms SLT.Zoo.LeadingMaps.R2_complexify
#print axioms SLT.Zoo.LeadingMaps.R3_complexify
#print axioms SLT.Zoo.LeadingMaps.cube_formC
#print axioms SLT.Zoo.LeadingMaps.eq_zero_iff_of_complexify
#print axioms SLT.Zoo.LeadingMaps.formC
#print axioms SLT.Zoo.LeadingMaps.lead_eq_zero_iff_four
#print axioms SLT.Zoo.LeadingMaps.lead_eq_zero_iff_three
#print axioms SLT.Zoo.LeadingMaps.lead_eq_zero_iff_two
#print axioms SLT.Zoo.LeadingMaps.leadingMap_complexify
#print axioms SLT.Zoo.LeadingMaps.row2C
#print axioms SLT.Zoo.LeadingMaps.row3C
#print axioms SLT.Zoo.LeadingMaps.rowC
#print axioms SLT.Zoo.LeadingMaps.rowCubic_rowC
#print axioms SLT.Zoo.LeadingMaps.twoCube_formC

/-! The position table from three inactive Laplace bounds (`Zoo/LossComparison.lean`), and the
source theorems of `VectorSLT/LossCompare` it uses. -/
#print axioms SLT.Zoo.LossComparison.H4_zero_eq_core
#print axioms SLT.Zoo.LossComparison.Hmid_one_zero_eq_core
#print axioms SLT.Zoo.LossComparison.Hmid_two_zero_eq_core
#print axioms SLT.Zoo.LossComparison.InactiveLaplace
#print axioms SLT.Zoo.LossComparison.ShellMargin
#print axioms SLT.Zoo.LossComparison.Zpos_upper_four
#print axioms SLT.Zoo.LossComparison.Zpos_upper_middle
#print axioms SLT.Zoo.LossComparison.Zpos_upper_of_marginData
#print axioms SLT.Zoo.LossComparison.angularMargin_G4
#print axioms SLT.Zoo.LossComparison.angularMargin_Gmid
#print axioms SLT.Zoo.LossComparison.inactiveLaplace_G4_of_shellMargin
#print axioms SLT.Zoo.LossComparison.inactiveLaplace_Gmid_of_shellMargin
#print axioms SLT.Zoo.LossComparison.inactiveLaplace_of_angularMargin
#print axioms SLT.Zoo.LossComparison.mainTheorem_shear_of_inactiveLaplace
#print axioms SLT.Zoo.LossComparison.mainTheorem_shear_of_shellMargin
#print axioms SLT.Zoo.LossComparison.marginModel_eq_mul
#print axioms SLT.Zoo.LossComparison.marginModel_laplaceUpper_of_inactive
#print axioms SLT.Zoo.LossComparison.norm_sq_complexify
#print axioms SLT.Zoo.LossComparison.positionMargin_of_marginData
#print axioms SLT.Zoo.LossComparison.thmKUpper_of_inactiveLaplace
#print axioms SLT.Zoo.LossComparison.thmK_of_upper
#print axioms SLT.Zoo.LossComparison.thmN_of_inactiveLaplace
#print axioms VectorSLT.LossCompare.position_four_marginData
#print axioms VectorSLT.LossCompare.middle_marginData
#print axioms VectorSLT.LossCompare.position_four_homogeneity
#print axioms VectorSLT.LossCompare.position_two_homogeneity
#print axioms VectorSLT.LossCompare.position_three_homogeneity
