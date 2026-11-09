module

public import ArtinMatthews.CubicThetaActualTransformation
public import ArtinMatthews.CubicThetaConstructedWeil


set_option backward.privateInPublic true
@[expose] public section

/-! The actual cubic Hecke theta congruence law, specialized to the proved
real, finite, and adelic Weil construction. No representation is a hypothesis. -/
noncomputable section
namespace ArtinMatthews

open scoped MatrixGroups
open Complex UpperHalfPlane

/-- The exact transformation at the compatible level `6 M²`, using the
genuinely constructed Weil representation rather than assumed covariance. -/
theorem cubicNumeratorHeckeTheta_constructed_transform
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    (M : ℕ) [NeZero M] (heven : 2 ∣ M) (hdiv : 9 * A ∣ (M : ℤ))
    (γ : SL(2, ℤ)) (hc : 6 * (M : ℤ) ^ 2 ∣ γ 1 0) (τ : ℍ) :
    heckeTheta (cubicNumeratorHeckeCharacter A hA) (γ • τ) =
      cubicThetaNebentypus (γ 1 1) * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) *
        heckeTheta (cubicNumeratorHeckeCharacter A hA) τ :=
  cubicNumeratorHeckeTheta_transform cubicThetaWeilData A hA hnoncube M heven hdiv γ hc τ

end ArtinMatthews
