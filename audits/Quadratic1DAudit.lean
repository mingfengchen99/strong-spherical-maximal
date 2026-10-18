import Quadratic1D

/-! Axiom audit of public declarations in Quadratic1D.lean.
Private dependencies are included transitively by `#print axioms`. -/

#print axioms StrongSpherical.Quadratic1D.phase
#print axioms StrongSpherical.Quadratic1D.slope
#print axioms StrongSpherical.Quadratic1D.wave
#print axioms StrongSpherical.Quadratic1D.hasDerivAt_phase
#print axioms StrongSpherical.Quadratic1D.hasDerivAt_slope
#print axioms StrongSpherical.Quadratic1D.hasDerivAt_wave
#print axioms StrongSpherical.Quadratic1D.continuous_wave
#print axioms StrongSpherical.Quadratic1D.norm_wave
#print axioms StrongSpherical.Quadratic1D.intervalIntegrable_wave
#print axioms StrongSpherical.Quadratic1D.norm_integral_wave_le_length
#print axioms StrongSpherical.Quadratic1D.norm_integral_wave_le_of_slope
#print axioms StrongSpherical.Quadratic1D.norm_integral_wave_le_of_quadratic
#print axioms StrongSpherical.Quadratic1D.centeredWave
#print axioms StrongSpherical.Quadratic1D.centeredWave_eq_exp
#print axioms StrongSpherical.Quadratic1D.centered_slope
#print axioms StrongSpherical.Quadratic1D.oscillationConstant
#print axioms StrongSpherical.Quadratic1D.oscillationConstant_pos
#print axioms StrongSpherical.Quadratic1D.norm_integral_centeredWave_le
#print axioms StrongSpherical.Quadratic1D.quadraticPhase
#print axioms StrongSpherical.Quadratic1D.norm_integral_quadraticPhase_le
#print axioms StrongSpherical.Quadratic1D.exists_uniform_subinterval_bound
#print axioms StrongSpherical.Quadratic1D.quadraticPrimitive
#print axioms StrongSpherical.Quadratic1D.hasDerivAt_quadraticPrimitive
#print axioms StrongSpherical.Quadratic1D.norm_quadraticPrimitive_le

/- Review the uniform quantifiers and the primitive interface. -/
#check StrongSpherical.Quadratic1D.exists_uniform_subinterval_bound
#check StrongSpherical.Quadratic1D.hasDerivAt_quadraticPrimitive
#check StrongSpherical.Quadratic1D.norm_quadraticPrimitive_le
