import SchurTest

/-! Transitive axiom audit of every public declaration written in SchurTest.lean. -/

#print axioms StrongSpherical.SchurTest.lintegral_weighted_sq_le
#print axioms StrongSpherical.SchurTest.lintegral_schur_sq_le
#print axioms StrongSpherical.SchurTest.kernelOperator
#print axioms StrongSpherical.SchurTest.measurable_kernelOperator
#print axioms StrongSpherical.SchurTest.lintegral_enorm_kernelOperator_sq_le
#print axioms StrongSpherical.SchurTest.eLpNorm_two_sq
#print axioms StrongSpherical.SchurTest.eLpNorm_kernelOperator_le
#print axioms StrongSpherical.SchurTest.memLp_kernelOperator
#print axioms StrongSpherical.SchurTest.norm_toLp_kernelOperator_le
#print axioms StrongSpherical.SchurTest.measurable_graphGap
#print axioms StrongSpherical.SchurTest.measurable_frequencyKernel
#print axioms StrongSpherical.SchurTest.measurable_inputKernel
#print axioms StrongSpherical.SchurTest.measurable_gramKernel
#print axioms StrongSpherical.SchurTest.schurConstant
#print axioms StrongSpherical.SchurTest.schurConstant_pos
#print axioms StrongSpherical.SchurTest.schur_scale_eq
#print axioms StrongSpherical.SchurTest.lintegral_row_le_of_spatialProfile
#print axioms StrongSpherical.SchurTest.lintegral_column_le_of_spatialProfile
#print axioms StrongSpherical.SchurTest.gramOperator_bound_of_spatialProfile
#print axioms StrongSpherical.SchurTest.exists_uniform_gramOperator_bound
#print axioms StrongSpherical.SchurTest.integrable_kernel_mul_ae
#print axioms StrongSpherical.SchurTest.kernelL2Apply
#print axioms StrongSpherical.SchurTest.kernelL2Apply_coe
#print axioms StrongSpherical.SchurTest.norm_kernelL2Apply_le
#print axioms StrongSpherical.SchurTest.kernelL2Apply_add
#print axioms StrongSpherical.SchurTest.kernelL2Apply_smul
#print axioms StrongSpherical.SchurTest.kernelL2Operator
#print axioms StrongSpherical.SchurTest.norm_kernelL2Operator_le
#print axioms StrongSpherical.SchurTest.kernelL2Operator_coe
#print axioms StrongSpherical.SchurTest.measurable_amplitude_of_fibers
#print axioms StrongSpherical.SchurTest.exists_uniform_gramL2Operator

/- Inspect the actual integral and L2 operators and the uniform quantifiers. -/
#print StrongSpherical.SchurTest.kernelOperator
#print StrongSpherical.SchurTest.kernelL2Apply
#print StrongSpherical.SchurTest.kernelL2Operator
#check StrongSpherical.SchurTest.lintegral_weighted_sq_le
#check StrongSpherical.SchurTest.lintegral_schur_sq_le
#check StrongSpherical.SchurTest.integrable_kernel_mul_ae
#check StrongSpherical.SchurTest.kernelL2Operator_coe
#check StrongSpherical.SchurTest.norm_kernelL2Operator_le
#check StrongSpherical.SchurTest.measurable_amplitude_of_fibers
#check StrongSpherical.SchurTest.schur_scale_eq
#check StrongSpherical.SchurTest.exists_uniform_gramL2Operator
