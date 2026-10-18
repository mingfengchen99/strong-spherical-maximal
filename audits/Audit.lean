import Definitions

/-! Axiom audit of every named declaration in Definitions.lean. -/

#print axioms StrongSpherical.Space
#print axioms StrongSpherical.UnitSphere
#print axioms StrongSpherical.Radii
#print axioms StrongSpherical.unitRadii
#print axioms StrongSpherical.localRadii
#print axioms StrongSpherical.unitRadii_mem_localRadii
#print axioms StrongSpherical.diagonalDilation
#print axioms StrongSpherical.diagonalDilation_apply
#print axioms StrongSpherical.continuous_diagonalDilation
#print axioms StrongSpherical.diagonalDilation_one
#print axioms StrongSpherical.inverseDilation
#print axioms StrongSpherical.inverseDilation_diagonalDilation
#print axioms StrongSpherical.diagonalDilation_inverseDilation
#print axioms StrongSpherical.dilationJacobian
#print axioms StrongSpherical.dilationJacobian_pos
#print axioms StrongSpherical.ellipsoidForm
#print axioms StrongSpherical.ellipsoid
#print axioms StrongSpherical.norm_sq_eq_sum_coordinates
#print axioms StrongSpherical.ellipsoidForm_eq_norm_sq
#print axioms StrongSpherical.continuous_ellipsoidForm
#print axioms StrongSpherical.measurableSet_ellipsoid
#print axioms StrongSpherical.diagonalDilation_mem_ellipsoid
#print axioms StrongSpherical.surfaceMeasure
#print axioms StrongSpherical.surfaceMeasure_isFiniteMeasure
#print axioms StrongSpherical.surfaceMeasure_ne_zero
#print axioms StrongSpherical.sphereMeasure
#print axioms StrongSpherical.sphereMeasure_isProbabilityMeasure
#print axioms StrongSpherical.sphericalMeasure
#print axioms StrongSpherical.sphericalMeasure_isProbabilityMeasure
#print axioms StrongSpherical.ellipsoidMeasure
#print axioms StrongSpherical.ellipsoidMeasure_isProbabilityMeasure
#print axioms StrongSpherical.ellipsoidMeasure_eq_map_sphere
#print axioms StrongSpherical.ellipsoidMeasure_compl_ellipsoid
#print axioms StrongSpherical.integral_ellipsoidMeasure
#print axioms StrongSpherical.measureConvolution
#print axioms StrongSpherical.sphericalAverage
#print axioms StrongSpherical.sphericalAverage_eq_sphere_integral
#print axioms StrongSpherical.maximalOver
#print axioms StrongSpherical.le_maximalOver
#print axioms StrongSpherical.maximalOver_mono
#print axioms StrongSpherical.strongSphericalMaximal
#print axioms StrongSpherical.strongSphericalMaximal_eq_sphere_integral
#print axioms StrongSpherical.localSphericalMaximal
#print axioms StrongSpherical.localSphericalMaximal_le_strong
#print axioms StrongSpherical.dilatedKernel
#print axioms StrongSpherical.kernelConvolution
#print axioms StrongSpherical.kernelConvolution_eq_integral
#print axioms StrongSpherical.localKernelMaximal
#print axioms StrongSpherical.strongKernelMaximal
#print axioms StrongSpherical.normalKernel
#print axioms StrongSpherical.dilatedNormalKernel
#print axioms StrongSpherical.criticalExponent
#print axioms StrongSpherical.StrongSphericalBound
#print axioms StrongSpherical.MainTheorem

/- The final project target is a Prop, with no proof asserted here. -/
#print StrongSpherical.StrongSphericalBound
#print StrongSpherical.MainTheorem
