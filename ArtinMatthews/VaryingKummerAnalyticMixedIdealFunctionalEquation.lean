module

public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualFlow
public import ArtinMatthews.VaryingKummerAnalyticMixedDualShift
public import ArtinMatthews.VaryingKummerAnalyticThetaRescaling


set_option backward.privateInPublic true
@[expose] public section

/-! The actual fractional-ideal xi functional equation in arbitrary signature.
The Euclidean trace-dual Gaussian is converted by its exact complex-place
radial scale and the actual affine unit-domain symmetry. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

theorem normalizedTheta_traceDual_rescale (u : logSpace K) (t : ℝ) :
    normalizedTheta (logScaledLattice (adjointEquiv (mixedIdealMatrix K I).symm)
      (mixedIdealLogScale K I (-u))) t =
    normalizedTheta (logScaledLattice (mixedIdealMatrix K (mixedTraceDualIdeal K I))
      (mixedIdealLogScale K (mixedTraceDualIdeal K I) (mixedDualLogShift K-u)))
      ((mixedDualRadialScale K)^2*t) := by
  rw [normalizedTheta_logScaled_adjoint_eq_traceDual,
    ← mixedIdealFlowTheta_eq_normalizedTheta]
  unfold mixedIdealFlowTheta
  simp_rw [← Complex.ofReal_pow, mixedIdealFlow_norm_sq, mixedDualGaussian_weight]
  apply tsum_congr
  intro b
  congr 1
  have H : (∑ w : InfinitePlace K,
      (mixedDualRadialScale K * mixedPlaceWeight K (mixedDualLogShift K-u) w * w (b : K))^2) =
      (mixedDualRadialScale K)^2 * ∑ w : InfinitePlace K,
        (mixedPlaceWeight K (mixedDualLogShift K-u) w * w (b : K))^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [H]
  push_cast
  ring

theorem mixedIdealFlowXi_functional_equation (u : logSpace K) (s : ℂ) :
    thetaMellinXi (logScaledLattice (mixedIdealMatrix K I) (mixedIdealLogScale K I u))
        ((Module.finrank ℚ K : ℂ)*s/2) =
      (((FractionalIdeal.absNorm I.1 : ℝ)*mixedDiscriminantScale K : ℝ) : ℂ)⁻¹ *
      (((mixedDualRadialScale K)^2 : ℝ) : ℂ)^(-((Module.finrank ℚ K : ℂ)*(1-s)/2)) *
      thetaMellinXi
        (logScaledLattice (mixedIdealMatrix K (mixedTraceDualIdeal K I))
          (mixedIdealLogScale K (mixedTraceDualIdeal K I) (mixedDualLogShift K-u)))
        ((Module.finrank ℚ K : ℂ)*(1-s)/2) := by
  rw [thetaMellinXi_functional_equation, adjointEquiv_logScaledLattice,
    ← mixedIdealLogScale_neg, mixedIdealIndex_card]
  have hz : (Module.finrank ℚ K : ℂ)/2-(Module.finrank ℚ K : ℂ)*s/2 =
      (Module.finrank ℚ K : ℂ)*(1-s)/2 := by ring
  rw [hz, thetaMellinXi_eq_of_normalizedTheta_rescale _ _
    (by simp only [mixedIdealIndex_card])
    (sq_pos_of_pos (mixedDualRadialScale_pos K)) (normalizedTheta_traceDual_rescale K I u)]
  rw [logScaledLattice_det, mixedIdealLogScale_sum, Real.exp_zero, one_mul,
    abs_inv, mixedIdealMatrix_abs_det]
  simp only [mixedDiscriminantScale, Complex.ofReal_inv, mul_assoc]

/-- Actual ideal-level functional equation, retaining the exact signature scale.
There is no restriction on real/complex signature or degree parity. -/
theorem mixedIdealUnitXi_functional_equation (s : ℂ) :
    mixedIdealUnitXi K I s =
      (((FractionalIdeal.absNorm I.1 : ℝ)*mixedDiscriminantScale K : ℝ) : ℂ)⁻¹ *
      (((mixedDualRadialScale K)^2 : ℝ) : ℂ)^(-((Module.finrank ℚ K : ℂ)*(1-s)/2)) *
        mixedIdealUnitXi K (mixedTraceDualIdeal K I) (1-s) := by
  unfold mixedIdealUnitXi
  simp_rw [mixedIdealFlowXi_functional_equation K I]
  rw [integral_const_mul]
  exact congrArg (fun z : ℂ =>
      (((FractionalIdeal.absNorm I.1 : ℝ)*mixedDiscriminantScale K : ℝ) : ℂ)⁻¹ *
      (((mixedDualRadialScale K)^2 : ℝ) : ℂ)^(-((Module.finrank ℚ K : ℂ)*(1-s)/2)) * z)
    (mixedIdealUnitXi_reflection K (mixedTraceDualIdeal K I) (mixedDualLogShift K) (1-s))

end
end ArtinMatthews.VaryingKummerAnalytic
