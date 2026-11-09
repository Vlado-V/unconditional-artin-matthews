module

public import ArtinMatthews.SixthKummerSharpRay
public import ArtinMatthews.IdealRayPrimitivePresentation
public import ArtinMatthews.KummerRowFrobeniusTransfer


set_option backward.privateInPublic true
@[expose] public section

/-! Primitive conductor descent of the actual individual Kummer
character at the proved ideal m_S*rad_S(u), retaining the full original
prime-to-ideal values and the exact old-modulus coefficient mask. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical
noncomputable section

variable {F : Type} [Field F] [NumberField F] [Algebra F ℂ]
variable [NumberField.IsTotallyComplex F]

theorem exists_sixthKummer_primitive_conductor {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : sixthWildPrimes F ⊆ S) (u : Fˣ) :
    ∃ (f : Ideal (𝓞 F)) (_hf : f ≠ ⊥) (_hMf : sixthKummerSharpIdeal S u ≤ f)
      (Ψ : EvenIdealRayCharacter F f),
      IsPrimitiveOnIdeals Ψ.residue ∧
      f.absNorm ≤ (sixthKummerFixedIdeal S).absNorm*(sixthExteriorRadicalIdeal S u).absNorm ∧
      (∀ I : RayClass.primeToModulusIdeals (integralIdealRayModulus (sixthKummerSharpIdeal S u)
          (sixthKummerSharpIdeal_ne_zero S u)),
        Ψ.idealHom (I:FractionalIdealGroup F)=
          GaloisIdealCharacter.idealHom F (sixthKummerRowField {(u:F)})
            (sixthKummerRowCharacter hζ {(u:F)} (u:F) (Finset.mem_singleton_self _) u.ne_zero)
            (I:FractionalIdealGroup F)) ∧
      ∀ I : Ideal (𝓞 F),
        (sixthKummerSharpRayCharacter hζ S hS u).allCoefficient I=
          if IsCoprime I (sixthKummerSharpIdeal S u) then Ψ.allCoefficient I else 0 := by
  let ψ := sixthKummerSharpRayCharacter hζ S hS u
  obtain ⟨f,hf,hMf,Ψ,hprim,hnorm,_hmask,hagree⟩ :=
    ψ.exists_primitive_idealCharacter (sixthKummerSharpIdeal_ne_zero S u)
  refine ⟨f,hf,hMf,Ψ,hprim,hnorm.trans_eq (sixthKummerSharpIdeal_absNorm S u),?_,?_⟩
  · intro I
    exact (hagree I).trans (DFunLike.congr_fun
      (sixthKummerSharpRayCharacter_idealHom hζ S hS u) (I:FractionalIdealGroup F))
  · exact ψ.primitiveIdeal_allCoefficient_mask (sixthKummerSharpIdeal_ne_zero S u) f hMf Ψ hagree

theorem exists_sixthKummer_primitive_nonprincipal_conductor {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : sixthWildPrimes F ⊆ S) (u : Fˣ)
    (hu : ¬∃ t : F, t^6=(u:F)) :
    ∃ (f : Ideal (𝓞 F)) (_hf : f ≠ ⊥) (_hMf : sixthKummerSharpIdeal S u ≤ f)
      (Ψ : EvenIdealRayCharacter F f),
      IsPrimitiveOnIdeals Ψ.residue ∧ Ψ.IsNonprincipal ∧
      f.absNorm ≤ (sixthKummerFixedIdeal S).absNorm*(sixthExteriorRadicalIdeal S u).absNorm ∧
      (∀ I : RayClass.primeToModulusIdeals (integralIdealRayModulus (sixthKummerSharpIdeal S u)
          (sixthKummerSharpIdeal_ne_zero S u)),
        Ψ.idealHom (I:FractionalIdealGroup F)=
          GaloisIdealCharacter.idealHom F (sixthKummerRowField {(u:F)})
            (sixthKummerRowCharacter hζ {(u:F)} (u:F) (Finset.mem_singleton_self _) u.ne_zero)
            (I:FractionalIdealGroup F)) ∧
      ∀ I : Ideal (𝓞 F),
        (sixthKummerSharpRayCharacter hζ S hS u).allCoefficient I=
          if IsCoprime I (sixthKummerSharpIdeal S u) then Ψ.allCoefficient I else 0 := by
  let ψ := sixthKummerSharpRayCharacter hζ S hS u
  obtain ⟨f,hf,hMf,Ψ,hprim,hΨ,hnorm,_hmask,hagree,hcoeff⟩ :=
    ψ.exists_primitive_nonprincipal_idealCharacter (sixthKummerSharpIdeal_ne_zero S u)
      (sixthKummerSharpRayCharacter_isNonprincipal hζ S hS u hu)
  refine ⟨f,hf,hMf,Ψ,hprim,hΨ,hnorm.trans_eq (sixthKummerSharpIdeal_absNorm S u),?_,hcoeff⟩
  intro I
  exact (hagree I).trans (DFunLike.congr_fun
    (sixthKummerSharpRayCharacter_idealHom hζ S hS u) (I:FractionalIdealGroup F))

theorem sixthKummer_primitive_common_ideal_value {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (u : Fˣ)
    (A : Finset F) (huA : (u:F) ∈ A)
    {f : Ideal (𝓞 F)} (Ψ : EvenIdealRayCharacter F f)
    (hagree : ∀ I : RayClass.primeToModulusIdeals (integralIdealRayModulus (sixthKummerSharpIdeal S u)
        (sixthKummerSharpIdeal_ne_zero S u)),
      Ψ.idealHom (I:FractionalIdealGroup F)=
        GaloisIdealCharacter.idealHom F (sixthKummerRowField {(u:F)})
          (sixthKummerRowCharacter hζ {(u:F)} (u:F) (Finset.mem_singleton_self _) u.ne_zero)
          (I:FractionalIdealGroup F))
    (I : RayClass.primeToModulusIdeals (integralIdealRayModulus (sixthKummerSharpIdeal S u)
      (sixthKummerSharpIdeal_ne_zero S u)))
    (hI : (I:FractionalIdealGroup F) ∈ RayClass.primeToModulusIdeals (rationalIdealRayModulus F
      (discriminantDegreeModulus F (sixthKummerRowField A)))) :
    Ψ.idealHom (I:FractionalIdealGroup F)=
      (sixthKummerRowRayCharacter hζ A (u:F) huA u.ne_zero).idealHom (I:FractionalIdealGroup F) := by
  have h := sixthKummerRow_rayIdealHom_eq_individual hζ A (u:F) huA u.ne_zero ⟨I,hI⟩
  rw [sixthKummerRowRayCharacter_idealHom] at h
  exact (hagree I).trans h.symm

end
end ArtinMatthews
