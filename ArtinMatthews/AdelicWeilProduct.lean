module

public import ArtinMatthews.BareRationalFourier
public import ArtinMatthews.AdelicWeilIndex
public import OAI.RepresentationTheory.Weil.AdelicSplitting.WeightedGaussianReciprocity


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine adelic quadratic Weil product, from the constructed bare
rational Fourier family and the actual adelic Poisson proof. -/

namespace ArtinMatthews.QuadraticWeil

open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F]
  (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
  (d : AdelicCharacterData F ψ)

include d in
theorem adelicGaussianIndex_hasProd (b : F) (hb : b ≠ 0) :
    HasProd (fun v : ArchimedeanAdeles.Construction.Places F =>
      OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex
        (ArchimedeanAdeles.Construction.Completion F v)
        (Characters.Construction.localAdditiveCharacter F ψ v)
        (ArchimedeanAdeles.Construction.rationalScalar F v b)) 1 := by
  have h := WeightedGaussianReciprocity.Construction.gaussianIndex_rational_power_hasProd
    F 1 ψ d.continuous d.unitary d.principal d.local_nontrivial
    (character_positionHaar F ψ d 1) b hb
    (bareRationalFourierFamily F ψ d 1) (bareRationalFourierFamily_spec F ψ d 1)
  simpa only [pow_one] using h

include d in
theorem adelicNormalizedWeil_hasProd (x : Fˣ) : HasProd (adelicNormalizedWeil F ψ x) 1 := by
  have hnum := adelicGaussianIndex_hasProd F ψ d (2 * (x : F))
    (mul_ne_zero (by norm_num) x.ne_zero)
  have hden := adelicGaussianIndex_hasProd F ψ d 2 (by norm_num)
  have h := hnum.mul (hden.inv₀ one_ne_zero)
  change HasProd (fun v => adelicNormalizedWeil F ψ x v) 1
  simpa only [adelicNormalizedWeil, map_mul, map_ofNat, inv_one, mul_one, div_eq_mul_inv] using h

end

end ArtinMatthews.QuadraticWeil
