module

public import ArtinMatthews.CubicThetaWeilTransform
public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.WeilData


set_option backward.privateInPublic true
@[expose] public section

/-!
The actual constructed Weil representation for the two-dimensional Eisenstein
lattice. No existence of a representation, theta transformation, or CuspForm
is a hypothesis. Congruence eigenvalues of its finite operator remain separate.
-/
noncomputable section
namespace ArtinMatthews

open scoped MatrixGroups
open Complex UpperHalfPlane
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-- The existing explicit real/finite/adelic construction in dimension two. -/
def cubicThetaWeilData :=
  OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.WeilData.CM.weilData 2

/-- The actual Hecke ideal theta satisfies the constructed rational Weil
transformation with its finite operator left explicit. -/
theorem heckeTheta_constructed_transform (γ : SL(2, ℚ))
    (χ : OAI.SevenEighths.HeckeFamily.Character) (hχ : χ.residue ≠ 1) (τ : ℍ) :
    theta (cubicThetaWeilData.finiteAction (eisensteinSymplectic γ)
      (eisensteinFiniteTest (OAI.SevenEighths.HeckeFamily.coefficients χ)))
        (eisensteinSiegel (γ • τ)) 0 =
      halfDet (realBlocks (eisensteinSymplectic γ)) (eisensteinSiegel τ) *
        (6 * heckeTheta χ τ) :=
  heckeTheta_adelic_transform cubicThetaWeilData γ χ hχ τ

end ArtinMatthews
