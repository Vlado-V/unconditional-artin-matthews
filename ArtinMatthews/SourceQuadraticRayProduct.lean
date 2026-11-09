module

public import ArtinMatthews.SourceQuadraticPrimitiveProduct
public import ArtinMatthews.SourceQuadraticClassFactorization


set_option backward.privateInPublic true
@[expose] public section

/-! The primitive product conductor on actual fixed ray-class slices. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀

theorem sourceQuadraticConductor_product_of_rayClass_eq (e f : E)
    (he : ∀ P, e P ≤ 1) (hf : ∀ P, f P ≤ 1) (hd : Disjoint e.support f.support)
    (hclass : sourcePrimeExponentRayClass F S₀ e = sourcePrimeExponentRayClass F S₀ f) :
    sourceQuadraticConductor F S₀ hζ (e + f) =
      sourcePrimeExponentIdeal F S₀ e * sourcePrimeExponentIdeal F S₀ f :=
  sourceQuadraticConductor_eq_product_of_class_eq F S₀ hζ e f he hf hd
    (sourcePrimeExponentRayClass_eq_localClass F S₀ hζ e f hclass)

variable [IsTotallyComplex F]

theorem sourceQuadraticRayClass_primitive_product (e f : E)
    (he : ∀ P, e P ≤ 1) (hf : ∀ P, f P ≤ 1) (hd : Disjoint e.support f.support)
    (hclass : sourcePrimeExponentRayClass F S₀ e = sourcePrimeExponentRayClass F S₀ f) :
    OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals
        (sourceQuadraticRayCharacter F S₀ hζ (e + f)).residue ∧
      sourceQuadraticConductor F S₀ hζ (e + f) =
        sourcePrimeExponentIdeal F S₀ e * sourcePrimeExponentIdeal F S₀ f ∧
      (let m := integralIdealRayModulus (sourceQuadraticProductModulus F S₀ e f)
          (sourceQuadraticProductModulus_ne_bot F S₀ e f)
       ((sourceQuadraticRayCharacter F S₀ hζ (e + f)).idealHom.comp
           (RayClass.primeToModulusIdeals m).subtype) =
         ((sourceQuadraticRayCharacter F S₀ hζ e).idealHom.comp
           (RayClass.primeToModulusIdeals m).subtype) *
         ((sourceQuadraticRayCharacter F S₀ hζ f).idealHom.comp
           (RayClass.primeToModulusIdeals m).subtype)) :=
  ⟨sourceQuadraticRayCharacter_primitive F S₀ hζ _,
    sourceQuadraticConductor_product_of_rayClass_eq F S₀ hζ e f he hf hd hclass,
    sourceQuadraticPrimitive_product_agreement F S₀ hζ e f he hf hd⟩

end
end ArtinMatthews.SourceEulerAssembly
