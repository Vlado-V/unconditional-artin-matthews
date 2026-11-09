module

public import ArtinMatthews.CubicThetaAdelicIdentity
public import ArtinMatthews.CubicThetaSiegelTransform
public import OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic


set_option backward.privateInPublic true
@[expose] public section

/-!
Restriction of the existing rational Gaussian theta transformation to the
actual Eisenstein Siegel line. The finite Weil operator remains explicit;
scalar congruence covariance is a separate arithmetic conclusion.
-/
noncomputable section
namespace ArtinMatthews

open scoped MatrixGroups
open Complex UpperHalfPlane
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

/-- The genuine rational symplectic transformation, restricted to the
positive Eisenstein quadratic form and with zero Jacobi argument. -/
theorem eisensteinAdelicTheta_transform
    (D : WeilData (Fin 2) MpR MpF MpA) (γ : SL(2, ℚ))
    (φ : finiteSchwartz (Fin 2)) (τ : ℍ) :
    theta (D.finiteAction (eisensteinSymplectic γ) φ) (eisensteinSiegel (γ • τ)) 0 =
      halfDet (realBlocks (eisensteinSymplectic γ)) (eisensteinSiegel τ) *
        theta φ (eisensteinSiegel τ) 0 := by
  have h := OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction.gaussian_theta_transformation
    D (eisensteinSymplectic γ) φ (eisensteinSiegel τ) 0
  simpa only [eisensteinSiegel_transform, map_zero, quadraticFactor_zero, one_mul] using h

/-- Actual Hecke ideal coefficients enter the rational Weil transformation
through the proved identity of the two convergent theta series. -/
theorem heckeTheta_adelic_transform
    (D : WeilData (Fin 2) MpR MpF MpA) (γ : SL(2, ℚ))
    (χ : OAI.SevenEighths.HeckeFamily.Character) (hχ : χ.residue ≠ 1) (τ : ℍ) :
    theta (D.finiteAction (eisensteinSymplectic γ)
      (eisensteinFiniteTest (OAI.SevenEighths.HeckeFamily.coefficients χ)))
        (eisensteinSiegel (γ • τ)) 0 =
      halfDet (realBlocks (eisensteinSymplectic γ)) (eisensteinSiegel τ) *
        (6 * heckeTheta χ τ) := by
  rw [eisensteinAdelicTheta_transform, theta_eisensteinFiniteTest_eq_six_heckeTheta χ hχ]

end ArtinMatthews
