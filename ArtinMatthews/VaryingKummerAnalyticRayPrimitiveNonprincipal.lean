module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealPrimitiveContinuation
public import ArtinMatthews.VaryingKummerAnalyticRayPrimitiveIdealSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine nonprincipality survives conductor descent, witnessed by the
same nonzero ideal coprime to the original modulus. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField RayClass IsDedekindDomain FractionalIdeal
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace EvenRayCharacter
variable {N : ℕ} [NeZero N] (ψ : EvenRayCharacter K N)

theorem primitiveIdeal_isNonprincipal (f : Ideal (𝓞 K))
    (hMf : rationalModulusIdeal (𝓞 K) N ≤ f) (Ψ : EvenIdealRayCharacter K f)
    (hagree : ∀ I : primeToModulusIdeals (rationalIdealRayModulus K N),
      Ψ.idealHom (I:FractionalIdealGroup K) = ψ.idealHom (I:FractionalIdealGroup K))
    (hnp : ψ.IsNonprincipal) : Ψ.IsNonprincipal := by
  obtain ⟨I,hI,hcop,hval⟩ := hnp
  have hcopf : IsCoprime I f :=
    hcop.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hMf)
  refine ⟨I,hI,hcopf,?_⟩
  have H := hagree (integralIdealPrimeToIdeal (rationalModulusIdeal (𝓞 K) N)
    (rationalModulusIdeal_ne_bot N) I hI hcop)
  change Ψ.idealHom (integralIdealFractionalUnit I hI) =
    ψ.idealHom (integralIdealFractionalUnit I hI) at H
  rwa [H]

theorem exists_primitive_nonprincipal_idealCharacter (hnp : ψ.IsNonprincipal) :
    ∃ (f : Ideal (𝓞 K)) (_hf : f ≠ ⊥)
      (_hMf : rationalModulusIdeal (𝓞 K) N ≤ f) (Ψ : EvenIdealRayCharacter K f),
      IsPrimitiveOnIdeals Ψ.residue ∧ Ψ.IsNonprincipal ∧
      f.absNorm ≤ (rationalModulusIdeal (𝓞 K) N).absNorm ∧
      (∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a) =
        if IsUnit (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a)
          then Ψ.residue (Ideal.Quotient.mk f a) else 0) ∧
      ∀ I : primeToModulusIdeals (rationalIdealRayModulus K N),
        Ψ.idealHom (I:FractionalIdealGroup K) = ψ.idealHom (I:FractionalIdealGroup K) := by
  obtain ⟨f,hf,hMf,Ψ,hprim,hnorm,hmask,hagree⟩ := ψ.exists_primitive_idealCharacter
  exact ⟨f,hf,hMf,Ψ,hprim,ψ.primitiveIdeal_isNonprincipal f hMf Ψ hagree hnp,
    hnorm,hmask,hagree⟩

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
