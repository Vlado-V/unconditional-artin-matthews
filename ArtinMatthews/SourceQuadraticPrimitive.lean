module

public import ArtinMatthews.SourceQuadraticConductor
public import ArtinMatthews.ArtinRayFaithfulPrimitive
public import ArtinMatthews.ArtinRayQuadraticSign
public import ArtinMatthews.QuadraticKummerNontrivial


set_option backward.privateInPublic true
@[expose] public section

/-! The exact primitive, quadratic character for each actual source
generator. A nonempty squarefree exterior support gives degree two
and a nonprincipal character. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic AngularLambda
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀

private theorem squarefree_has_one (e : E) (he : ∀ P, e P ≤ 1) (hne : e ≠ 0) :
    ∃ P : SourceExteriorPrime F S₀, e P = 1 := by
  by_contra h
  push Not at h
  apply hne
  ext P
  have hP := he P
  have hn := h P
  simp only [Finsupp.zero_apply]
  omega

theorem sourceQuadraticField_finrank_two (e : E) (he : ∀ P, e P ≤ 1) (hne : e ≠ 0) :
    Module.finrank F (SourceQuadraticField F S₀ hζ e) = 2 := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  obtain ⟨P, hP⟩ := squarefree_has_one F S₀ e he hne
  apply quadraticKummerField_finrank_eq_two_of_valuation_one (sourcePrimitiveRootSix F hζ)
    (sourcePrimeExponentUnit F hζ S₀ e) P.val
  rw [sourcePrimeExponentUnit_val, sourcePrimeExponentGenerator_valuation, hP]
  rfl

variable [IsTotallyComplex F]

theorem sourceQuadraticRayCharacter_primitive (e : E) :
    OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals (sourceQuadraticRayCharacter F S₀ hζ e).residue := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  let : IsAbelianGalois F (SourceQuadraticField F S₀ hζ e) :=
    sourceQuadraticField_isAbelianGalois F S₀ hζ e
  exact ArtinRay.abelianNormConductorRayCharacter_primitive
    (sourceQuadraticGaloisCharacter F S₀ hζ e) (quadraticKummerCharacter_injective _ _)

theorem sourceQuadraticRayCharacter_sq (e : E) (I : FractionalIdealGroup F) :
    (sourceQuadraticRayCharacter F S₀ hζ e).idealHom I ^ 2 = 1 := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  let : IsAbelianGalois F (SourceQuadraticField F S₀ hζ e) :=
    sourceQuadraticField_isAbelianGalois F S₀ hζ e
  exact ArtinRay.abelianNormConductorRayCharacter_pow
    (sourceQuadraticGaloisCharacter F S₀ hζ e) 2
    (quadraticKummerCharacter_sq _ _) I

theorem sourceQuadraticRayCharacter_isNonprincipal (e : E) (he : ∀ P, e P ≤ 1) (hne : e ≠ 0) :
    (sourceQuadraticRayCharacter F S₀ hζ e).IsNonprincipal := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  let : IsAbelianGalois F (SourceQuadraticField F S₀ hζ e) :=
    sourceQuadraticField_isAbelianGalois F S₀ hζ e
  apply ArtinRay.abelianNormConductorRayCharacter_isNonprincipal
  obtain ⟨P, hP⟩ := squarefree_has_one F S₀ e he hne
  apply quadraticKummerCharacter_ne_one_of_valuation_one (sourcePrimitiveRootSix F hζ)
    (sourcePrimeExponentUnit F hζ S₀ e) P.val
  rw [sourcePrimeExponentUnit_val, sourcePrimeExponentGenerator_valuation, hP]
  rfl

end
end ArtinMatthews.SourceEulerAssembly
