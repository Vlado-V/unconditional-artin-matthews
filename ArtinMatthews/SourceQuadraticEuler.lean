module

public import ArtinMatthews.SourceQuadraticPrimitive
public import ArtinMatthews.SourceQuadraticConductorProduct
public import ArtinMatthews.QuadraticKummerEuler
public import ArtinMatthews.VaryingKummerAnalyticDedekindSeriesClasses


set_option backward.privateInPublic true
@[expose] public section

/-! The actual source family's principal branch and its nonprincipal
two-factor Dedekind identity on the half-plane of absolute convergence. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic AngularLambda
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀

theorem sourceQuadraticGaloisCharacter_zero : sourceQuadraticGaloisCharacter F S₀ hζ 0 = 1 := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  apply (quadraticKummerCharacter_one_iff (sourcePrimitiveRootSix F hζ)
    (sourcePrimeExponentUnit F hζ S₀ 0)).mpr
  refine ⟨1, ?_⟩
  rw [sourcePrimeExponentUnit_zero, Units.val_one, one_pow]

theorem sourceQuadraticConductor_zero : sourceQuadraticConductor F S₀ hζ 0 = 1 := by
  rw [sourceQuadraticConductor_eq_exterior_of_localSquares F S₀ hζ 0
    (by intro P; simp) (by
      intro P _
      refine ⟨1, ?_⟩
      rw [sourcePrimeExponentUnit_zero, Units.val_one, map_one, one_pow])]
  simp [sourcePrimeExponentIdeal]

variable [IsTotallyComplex F]

theorem sourceQuadraticRayCharacter_zero_idealHom (I : FractionalIdealGroup F) :
    (sourceQuadraticRayCharacter F S₀ hζ 0).idealHom I = 1 := by
  rw [sourceQuadraticRayCharacter_idealHom, sourceQuadraticGaloisCharacter_zero]
  change (∏ᶠ P : HeightOneSpectrum (𝓞 F),
    (1 : ℂˣ) ^ FractionalIdeal.count F P I.val) = 1
  simp only [one_zpow, finprod_one]

theorem sourceQuadraticRayCharacter_zero_coefficient (J : integralFractionalIdeals F) :
    (sourceQuadraticRayCharacter F S₀ hζ 0).coefficient J = 1 := by
  have hc : IsCoprime (EvenRayCharacter.underlyingIdeal J)
      (sourceQuadraticConductor F S₀ hζ 0) := by
    rw [sourceQuadraticConductor_zero]
    exact isCoprime_one_right
  simp only [EvenIdealRayCharacter.coefficient, ite_eq_left hc,
    sourceQuadraticRayCharacter_zero_idealHom, Units.val_one]

theorem sourceQuadraticRayCharacter_zero_dirichlet {s : ℂ} (hs : 1 < s.re) :
    (sourceQuadraticRayCharacter F S₀ hζ 0).dirichlet s = dedekindZeta F s := by
  rw [← integralDedekindDirichlet_eq_dedekindZeta F hs]
  unfold EvenIdealRayCharacter.dirichlet integralDedekindDirichlet
  simp only [sourceQuadraticRayCharacter_zero_coefficient, one_mul]

theorem sourceQuadraticRayCharacter_dedekind_factor (e : E) (he : ∀ P, e P ≤ 1) (hne : e ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta (SourceQuadraticField F S₀ hζ e) s =
      dedekindZeta F s * (sourceQuadraticRayCharacter F S₀ hζ e).dirichlet s := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  let : IsAbelianGalois F (SourceQuadraticField F S₀ hζ e) :=
    sourceQuadraticField_isAbelianGalois F S₀ hζ e
  exact ArtinRay.quadraticNormConductor_dedekind_factor
    (sourceQuadraticField_finrank_two F S₀ hζ e he hne)
    (sourceQuadraticGaloisCharacter F S₀ hζ e) (quadraticKummerCharacter_injective _ _) hs

end
end ArtinMatthews.SourceEulerAssembly
