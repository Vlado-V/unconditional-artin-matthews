module

public import ArtinMatthews.PrincipalAngularMellinSignal
public import ArtinMatthews.VaryingKummerAnalyticDedekindSeriesClasses


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine conductor-one principal ideal-ray character, and the exact
identification of its literal ideal series and finite Euler factors with
Dedekind zeta. This supplies the principal branch without a nonprincipal
continuation or an assumed Dirichlet-series identification. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal Set
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def principalAngularTrivialRay : EvenIdealRayCharacter K (⊤ : Ideal (𝓞 K)) where
  idealHom := 1
  finiteOrder := ⟨1, by norm_num, by intro J; simp⟩
  residue := 1
  principalLaw a _ ha := by
    simpa using (MulChar.one_apply ((quotient_isUnit_iff_span_coprime _ a).mpr ha)).symm

theorem principalAngularTrivialRay_coefficient (J : integralFractionalIdeals K) :
    (principalAngularTrivialRay K).coefficient J = 1 := by
  have hc : IsCoprime (EvenRayCharacter.underlyingIdeal J) (⊤ : Ideal (𝓞 K)) := by
    rw [← Ideal.one_eq_top]
    exact isCoprime_one_right
  simp [EvenIdealRayCharacter.coefficient, hc, principalAngularTrivialRay]

theorem principalAngularTrivialRay_allCoefficient {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) :
    (principalAngularTrivialRay K).allCoefficient J = 1 := by
  have hc : IsCoprime J (⊤ : Ideal (𝓞 K)) := by
    rw [← Ideal.one_eq_top]
    exact isCoprime_one_right
  simp [EvenIdealRayCharacter.allCoefficient, hJ, hc, principalAngularTrivialRay]

theorem principalAngularTrivialRay_dirichlet {s : ℂ} (hs : 1 < s.re) :
    (principalAngularTrivialRay K).dirichlet s = dedekindZeta K s := by
  rw [← integralDedekindDirichlet_eq_dedekindZeta K hs]
  unfold EvenIdealRayCharacter.dirichlet integralDedekindDirichlet
  simp only [principalAngularTrivialRay_coefficient, one_mul]

theorem principalAngularTrivialRay_euler (S : Finset (ArtinMatthews.ProbePrime K)) (s : ℂ) :
    principalAngularRayEulerFactor (principalAngularTrivialRay K) S s =
      principalZetaEulerFactor S s := by
  unfold principalAngularRayEulerFactor principalZetaEulerFactor
  apply Finset.prod_congr rfl
  intro P _
  rw [principalAngularTrivialRay_allCoefficient K P.ne_bot, one_mul]

theorem principalAngularTrivialRay_exterior (S : Finset (ArtinMatthews.ProbePrime K))
    {s : ℂ} (hs : 1 < s.re) :
    principalAngularExteriorL (principalAngularTrivialRay K) S s =
      principalExteriorZeta S s := by
  rw [principalAngularExteriorL, principalExteriorZeta, principalAngularTrivialRay_euler,
    principalAngularTrivialRay_dirichlet K hs, mixedDedekindZeta_eq K hs]

end
end ArtinMatthews.VaryingKummerAnalytic
