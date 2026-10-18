import GeometricDecay
import NormalPieceSummation
import SphericalDomination
import SphericalRegularity
import SphericalLInfinity
import SphericalLp
import Main

open MeasureTheory
open scoped ENNReal NNReal CompactlySupported

/-! Transitive axiom audit of all new public declarations, including the final theorem. -/

#print axioms StrongSpherical.GeometricDecay.dyadicWeight
#print axioms StrongSpherical.GeometricDecay.dyadicWeight_nonneg
#print axioms StrongSpherical.GeometricDecay.summable_dyadicWeight
#print axioms StrongSpherical.NormalPieceSummation.ennreal_rpow_iSup
#print axioms StrongSpherical.NormalPieceSummation.eLpNorm_tsum_le
#print axioms StrongSpherical.NormalPieceSummation.pieceSum
#print axioms StrongSpherical.NormalPieceSummation.exists_summable_piece_coefficients
#print axioms StrongSpherical.NormalPieceSummation.uniform_pieceSum_Lp
#print axioms StrongSpherical.NormalPieceSummation.pieceSum_ae_lt_top
#print axioms StrongSpherical.SphericalDomination.kernelConvolution_dilated_eq_pairing
#print axioms StrongSpherical.SphericalDomination.sphericalAverage_eq_pairing
#print axioms StrongSpherical.SphericalDomination.tendsto_partial_convolution
#print axioms StrongSpherical.SphericalDomination.partial_convolution_enorm_le_tsum
#print axioms StrongSpherical.SphericalDomination.sphericalAverage_enorm_le_tsum
#print axioms StrongSpherical.SphericalDomination.strongSphericalMaximal_le_tsum
#print axioms StrongSpherical.SphericalDomination.compact_strongSphericalMaximal_le_tsum
#print axioms StrongSpherical.SphericalRegularity.continuous_sphericalAverage
#print axioms StrongSpherical.SphericalRegularity.lowerSemicontinuous_strongSphericalMaximal
#print axioms StrongSpherical.SphericalRegularity.measurable_strongSphericalMaximal
#print axioms StrongSpherical.SphericalLInfinity.continuous_enorm_le_eLpNorm_top
#print axioms StrongSpherical.SphericalLInfinity.sphericalAverage_enorm_le
#print axioms StrongSpherical.SphericalLInfinity.strongSphericalMaximal_le
#print axioms StrongSpherical.SphericalLInfinity.eLpNorm_strongSphericalMaximal_top_le
#print axioms StrongSpherical.SphericalLInfinity.strongSphericalBound_top
#print axioms StrongSpherical.SphericalLp.critical_gt_one
#print axioms StrongSpherical.SphericalLp.strongSphericalBound_finite
#print axioms StrongSpherical.main_theorem
#print axioms StrongSpherical.strong_spherical_maximal_bound

/-! Main theorem and review entry points, with complete elaborated types. -/

#check StrongSpherical.GeometricDecay.summable_dyadicWeight
#check StrongSpherical.NormalPieceSummation.exists_summable_piece_coefficients
#check StrongSpherical.NormalPieceSummation.uniform_pieceSum_Lp
#check StrongSpherical.NormalPieceSummation.pieceSum_ae_lt_top
#check StrongSpherical.SphericalDomination.tendsto_partial_convolution
#check StrongSpherical.SphericalDomination.strongSphericalMaximal_le_tsum
#check StrongSpherical.SphericalRegularity.measurable_strongSphericalMaximal
#check StrongSpherical.SphericalLInfinity.strongSphericalBound_top
#check StrongSpherical.SphericalLp.strongSphericalBound_finite
#check StrongSpherical.main_theorem
#check StrongSpherical.strong_spherical_maximal_bound

/-! The unchanged original target and its fully expanded statement. -/

example : StrongSpherical.MainTheorem := StrongSpherical.main_theorem

example : ∀ (n : ℕ), 4 ≤ n → ∀ (p : ℝ≥0∞),
    StrongSpherical.criticalExponent n < p →
      ∃ C : ℝ≥0, ∀ f : C_c(StrongSpherical.Space n, ℂ),
        AEMeasurable (StrongSpherical.strongSphericalMaximal
          (f : StrongSpherical.Space n → ℂ)) volume ∧
        eLpNorm (StrongSpherical.strongSphericalMaximal
          (f : StrongSpherical.Space n → ℂ)) p volume ≤
            (C : ℝ≥0∞) * eLpNorm (f : StrongSpherical.Space n → ℂ) p volume :=
  StrongSpherical.main_theorem
