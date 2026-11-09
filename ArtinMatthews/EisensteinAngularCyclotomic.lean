module

public import ArtinMatthews.EisensteinAngularField
public import ArtinMatthews.EisensteinAngularArch
public import ArtinMatthews.EisensteinAngularProbe


set_option backward.privateInPublic true
@[expose] public section

/-! The complete angular character construction for a number field
containing a specified primitive twelfth root. No Eisenstein embedding,
prime-phase identity, or infinity type is supplied as a premise. -/
namespace ArtinMatthews.AngularLambda
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] [NumberField F] {ζ : F}

def cyclotomicAngularResidueCharacter (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 F)) (hsix : (6 : 𝓞 F) ∉ P.asIdeal) :
    MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ := by
  letI := baseAlgebraOfTwelve hζ
  exact globalAngularResidueCharacter F P hsix

theorem cyclotomicAngularResidueCharacter_order (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 F)) (hsix : (6 : 𝓞 F) ∉ P.asIdeal) :
    orderOf (cyclotomicAngularResidueCharacter hζ P hsix) = 6 := by
  let : Algebra BaseField F := baseAlgebraOfTwelve hζ
  exact globalAngularResidueCharacter_order F P hsix

theorem cyclotomicAngularResidueCharacter_gammaTwo (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 F)) (hsix : (6 : 𝓞 F) ∉ P.asIdeal) :
    probeIdealGaussGamma F P (cyclotomicAngularResidueCharacter hζ P hsix) 2 ^ 3 =
      -cyclotomicAngularIdeal hζ P.asIdeal := by
  let : Algebra BaseField F := baseAlgebraOfTwelve hζ
  exact globalAngularResidueCharacter_gammaTwo F P hsix

theorem cyclotomicAngularResidueCharacter_localLambda (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 F)) (hsix : (6 : 𝓞 F) ∉ P.asIdeal) :
    probeIdealGaussLocalLambda F P (cyclotomicAngularResidueCharacter hζ P hsix) =
      cyclotomicAngularIdeal hζ P.asIdeal := by
  let : Algebra BaseField F := baseAlgebraOfTwelve hζ
  exact globalAngularResidueCharacter_localLambda F P hsix

theorem cyclotomicAngularIdeal_norm (hζ : IsPrimitiveRoot ζ 12)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hc : IsCoprime I (Ideal.span {(3 : 𝓞 F)})) :
    ‖cyclotomicAngularIdeal hζ I‖ = 1 := by
  let : Algebra BaseField F := baseAlgebraOfTwelve hζ
  exact angularNormIdeal_norm F I hI hc

theorem cyclotomicAngularIdeal_infinityType (hζ : IsPrimitiveRoot ζ 12) :
    ∃ e : InfinitePlace F → ℤ,
      (∀ w, e w = 1 ∨ e w = -1) ∧
      ∀ a : 𝓞 F, a ≠ 0 → (3 : 𝓞 F) ∣ a-1 →
        cyclotomicAngularIdeal hζ (Ideal.span {a}) =
          ∏ w : InfinitePlace F, complexAngular (w.embedding (a : F)) ^ e w := by
  let : Algebra BaseField F := baseAlgebraOfTwelve hζ
  refine ⟨angularInfinityExponent F,angularInfinityExponent_eq_one_or_neg_one F,?_⟩
  intro a ha hthree
  exact angularNormIdeal_principal_infinityType F a ha hthree

theorem cyclotomicAngularResidueCharacter_outsideS (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ P, (6 : 𝓞 F) ∈ P.asIdeal → P ∈ S) (P : HeightOneSpectrum (𝓞 F))
    (hP : P ∉ S) :
    let hsix : (6 : 𝓞 F) ∉ P.asIdeal := fun h => hP (hS P h)
    probeIdealGaussLocalLambda F P (cyclotomicAngularResidueCharacter hζ P hsix) =
      cyclotomicAngularIdeal hζ P.asIdeal := by
  let : Algebra BaseField F := baseAlgebraOfTwelve hζ
  exact globalAngularResidueCharacter_outsideS F S hS P hP

end
end ArtinMatthews.AngularLambda
