module

public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.CubicReciprocityBridgeSymbol
public import ArtinMatthews.CubicReciprocityBridgePrimary
public import ArtinMatthews.CubicThetaCoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! Exact prime values of the actual finite-conductor cubic numerator character. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths
local notation "EO" => HeckeFamily.O

/-- At a prime away from `3A`, the actual numerator Hecke character has the
same value as the actual finite-field cubic residue character. -/
theorem cubicNumeratorHeckeCharacter_prime (A : ℤ) (hA : A ≠ 0)
    (P : Ideal EO) [P.IsMaximal] (hg : lambda ∉ P) (hAP : (A : EO) ∉ P) :
    thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) P =
      ConcreteTraceCRT.eisEmbedding (cubicChar P hg (Ideal.Quotient.mk P (A : EO))) := by
  obtain ⟨p, hP, hp0, hprimary⟩ := exists_cubicMoment_primary_generator P hg
  have hp : Prime p := (Ideal.span_singleton_prime hp0).mp (hP ▸ inferInstance)
  have hpE : CubicFirstMoment.primaryPrime (heckeIntegersEquivCubicEisenstein p) :=
    ⟨hprimary, (MulEquiv.prime_iff heckeIntegersEquivCubicEisenstein).mpr hp⟩
  calc
    thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) P =
        thetaIdealCharacter (cubicNumeratorHeckeCharacter A hA) (Ideal.span {p}) :=
      congrArg _ hP
    _ = HeckeFamily.elementCoeff (cubicNumeratorHeckeCharacter A hA) p :=
      thetaIdealCharacter_span _ hp0
    _ = CubicFirstMoment.cubicSymbol (heckeIntegersEquivCubicEisenstein p)
        (A : CubicFirstMoment.Eisenstein) :=
      cubicNumeratorHeckeCharacter_element_primary A hA p hprimary
    _ = ConcreteTraceCRT.eisEmbedding (cubicChar P hg (Ideal.Quotient.mk P (A : EO))) := by
      simpa only [map_intCast] using cubicSymbol_eq_actualCubicChar P hg hP hpE hAP

end ArtinMatthews
