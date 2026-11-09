module

public import ArtinMatthews.SourceQuadraticCoefficients
public import ArtinMatthews.SourceQuadraticConductorProduct
public import ArtinMatthews.SourceQuadraticSelfDual


set_option backward.privateInPublic true
@[expose] public section

/-! The character of the product radicand gives the exact exterior
coefficients of the product with the conjugate character. Equal local
square classes yield its literal primitive product conductor. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀

variable [IsTotallyComplex F]

theorem sourceQuadraticRayCharacter_reciprocity (e f : E)
    (he : ∀ P, e P ≤ 1) (hf : ∀ P, f P ≤ 1) :
    (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient (sourcePrimeExponentIdeal F S₀ f) =
      (sourceQuadraticRayCharacter F S₀ hζ f).allCoefficient (sourcePrimeExponentIdeal F S₀ e) := by
  rw [sourceQuadraticRayCharacter_allCoefficient F S₀ hζ e he,
    sourceQuadraticRayCharacter_allCoefficient F S₀ hζ f hf]
  exact sourceReflectionQuadraticSymbol_reciprocity F S₀ hζ f e

theorem sourceQuadraticRayCharacter_product_exterior (e f : E)
    (he : ∀ P, e P ≤ 1) (hf : ∀ P, f P ≤ 1) (hd : Disjoint e.support f.support) (d : E) :
    (sourceQuadraticRayCharacter F S₀ hζ (e + f)).allCoefficient (sourcePrimeExponentIdeal F S₀ d) =
      (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient (sourcePrimeExponentIdeal F S₀ d) *
        star ((sourceQuadraticRayCharacter F S₀ hζ f).allCoefficient (sourcePrimeExponentIdeal F S₀ d)) := by
  rw [sourceQuadraticRayCharacter_star_allCoefficient,
    sourceQuadraticRayCharacter_allCoefficient F S₀ hζ (e + f)
      (sourceQuadraticDisjoint_add_squarefree F S₀ e f he hf hd),
    sourceQuadraticRayCharacter_allCoefficient F S₀ hζ e he,
    sourceQuadraticRayCharacter_allCoefficient F S₀ hζ f hf]
  unfold sourceReflectionQuadraticSymbol
  rw [sourcePrimeExponentGenerator_add]
  exact (congrArg (fun z : ℂ => z ^ 3)
    (sourceReflectionExponentResidueValue_mul F S₀ hζ d
      (sourcePrimeExponentGenerator F hζ S₀ e) (sourcePrimeExponentGenerator F hζ S₀ f))).trans
    (mul_pow _ _ 3)

theorem sourceQuadratic_primitive_product_on_exterior (e f : E)
    (he : ∀ P, e P ≤ 1) (hf : ∀ P, f P ≤ 1) (hd : Disjoint e.support f.support)
    (hclass : sourceQuadraticLocalClass F S₀ hζ e = sourceQuadraticLocalClass F S₀ hζ f) :
    OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals
        (sourceQuadraticRayCharacter F S₀ hζ (e + f)).residue ∧
      sourceQuadraticConductor F S₀ hζ (e + f) =
        sourcePrimeExponentIdeal F S₀ e * sourcePrimeExponentIdeal F S₀ f ∧
      ∀ d : E, (sourceQuadraticRayCharacter F S₀ hζ (e + f)).allCoefficient
          (sourcePrimeExponentIdeal F S₀ d) =
        (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient (sourcePrimeExponentIdeal F S₀ d) *
          star ((sourceQuadraticRayCharacter F S₀ hζ f).allCoefficient (sourcePrimeExponentIdeal F S₀ d)) :=
  ⟨sourceQuadraticRayCharacter_primitive F S₀ hζ _,
    sourceQuadraticConductor_eq_product_of_class_eq F S₀ hζ e f he hf hd hclass,
    sourceQuadraticRayCharacter_product_exterior F S₀ hζ e f he hf hd⟩

end
end ArtinMatthews.SourceEulerAssembly
