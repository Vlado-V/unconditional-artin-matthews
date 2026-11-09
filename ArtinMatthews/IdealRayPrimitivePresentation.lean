module

public import ArtinMatthews.IdealRayPrimitivePrincipal
public import ArtinMatthews.VaryingKummerAnalyticRayIdealConductorOne
public import ArtinMatthews.VaryingKummerAnalyticRayIdealMultiplicativity


set_option backward.privateInPublic true
@[expose] public section

/-! Primitive descent at the actual ideal modulus. The finite-ring
conductor construction gives `M ≤ f` and `Norm f ≤ Norm M` directly.
The extension preserves every old prime-to ideal value; coefficients
retain the exact old-modulus zero mask. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField RayClass IsDedekindDomain FractionalIdeal
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace EvenIdealRayCharacter

variable {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)

theorem exists_primitive_idealRay_presentation :
    ∃ (f : Ideal (𝓞 K)) (hf : f ≠ ⊥) (hMf : M ≤ f)
      (φ : MulChar ((𝓞 K) ⧸ f) ℂ)
      (χ : IdealRayClassGroup (integralIdealRayModulus f hf) →* ℂˣ),
      IsPrimitiveOnIdeals φ ∧ f.absNorm ≤ M.absNorm ∧
      (∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk f a) else 0) ∧
      (∀ u : (𝓞 K)ˣ, φ (Ideal.Quotient.mk f (u : 𝓞 K)) = 1) ∧
      (∃ e : ℕ, 0 < e ∧ ∀ c, χ c ^ e = 1) ∧
      (∀ c, χ (conductorIdealProjection hM f hf hMf c) = ψ.rayClassCharacter hM c) ∧
      ∀ (a : 𝓞 K) (ha : a ≠ 0) (hac : IsCoprime (Ideal.span {a}) f),
        (χ (QuotientGroup.mk' (principalRayIdealSubgroup (integralIdealRayModulus f hf))
          (integralPrincipalPrimeToIdeal f hf a ha hac)) : ℂ) = φ (Ideal.Quotient.mk f a) := by
  obtain ⟨f, φ, hMf, hf, hprim, hnorm, hmask, _hfactor, hunit⟩ :=
    exists_primitive_residue_conductor_trivial_on_units M hM ψ.residue ψ.residue_unit
  exact ⟨f, hf, hMf, φ, ψ.descendedIdealRayCharacter hM f hf hMf φ hmask,
    hprim, hnorm, hmask, hunit,
    ψ.descendedIdealRayCharacter_finiteOrder hM f hf hMf φ hmask,
    ψ.descendedIdealRayCharacter_projection hM f hf hMf φ hmask,
    ψ.descendedIdealRayCharacter_principal hM f hf hMf φ hmask⟩

theorem exists_primitive_idealCharacter :
    ∃ (f : Ideal (𝓞 K)) (_hf : f ≠ ⊥) (_hMf : M ≤ f)
      (Ψ : EvenIdealRayCharacter K f),
      IsPrimitiveOnIdeals Ψ.residue ∧ f.absNorm ≤ M.absNorm ∧
      (∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then Ψ.residue (Ideal.Quotient.mk f a) else 0) ∧
      ∀ I : primeToModulusIdeals (integralIdealRayModulus M hM),
        Ψ.idealHom (I : FractionalIdealGroup K) = ψ.idealHom (I : FractionalIdealGroup K) := by
  obtain ⟨f, hf, hMf, φ, χ, hprim, hnorm, hmask, _hunit, hfinite, hagree, hprincipal⟩ :=
    ψ.exists_primitive_idealRay_presentation hM
  let Ψ := EvenIdealRayCharacter.ofIdealRayClass hf χ hfinite φ hprincipal
  refine ⟨f, hf, hMf, Ψ, hprim, hnorm, hmask, ?_⟩
  intro I
  let hnm := integralIdealRayModulus_antitone hM hf hMf
  have H := EvenIdealRayCharacter.ofIdealRayClass_idealHom_primeTo hf χ hfinite φ hprincipal
    (primeToIdealConductorInclusion hnm I)
  change Ψ.idealHom (I : FractionalIdealGroup K) = _ at H
  rw [← idealConductorProjection_ideal hnm I] at H
  exact H.trans ((hagree _).trans (ψ.rayClassCharacter_ideal hM I))

theorem primitiveIdeal_isNonprincipal (f : Ideal (𝓞 K)) (hMf : M ≤ f)
    (Ψ : EvenIdealRayCharacter K f)
    (hagree : ∀ I : primeToModulusIdeals (integralIdealRayModulus M hM),
      Ψ.idealHom (I : FractionalIdealGroup K) = ψ.idealHom (I : FractionalIdealGroup K))
    (hnp : ψ.IsNonprincipal) : Ψ.IsNonprincipal := by
  obtain ⟨I, hI, hcop, hval⟩ := hnp
  have hcopf : IsCoprime I f :=
    hcop.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hMf)
  refine ⟨I, hI, hcopf, ?_⟩
  have H := hagree (integralIdealPrimeToIdeal M hM I hI hcop)
  change Ψ.idealHom (integralIdealFractionalUnit I hI) =
    ψ.idealHom (integralIdealFractionalUnit I hI) at H
  rwa [H]

theorem primitiveIdeal_allCoefficient_mask (f : Ideal (𝓞 K)) (hMf : M ≤ f)
    (Ψ : EvenIdealRayCharacter K f)
    (hagree : ∀ I : primeToModulusIdeals (integralIdealRayModulus M hM),
      Ψ.idealHom (I : FractionalIdealGroup K) = ψ.idealHom (I : FractionalIdealGroup K))
    (I : Ideal (𝓞 K)) :
    ψ.allCoefficient I = if IsCoprime I M then Ψ.allCoefficient I else 0 := by
  by_cases hI : I = ⊥
  · subst I
    simp only [allCoefficient_bot, ite_self]
  simp only [allCoefficient, dite_eq_left hI]
  by_cases hcop : IsCoprime I M
  · have hcopf : IsCoprime I f :=
      hcop.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hMf)
    simp only [ite_eq_left hcop, ite_eq_left hcopf]
    exact congrArg Units.val (hagree (integralIdealPrimeToIdeal M hM I hI hcop)).symm
  · simp only [ite_eq_right hcop]

theorem exists_primitive_nonprincipal_idealCharacter (hnp : ψ.IsNonprincipal) :
    ∃ (f : Ideal (𝓞 K)) (_hf : f ≠ ⊥) (_hMf : M ≤ f)
      (Ψ : EvenIdealRayCharacter K f),
      IsPrimitiveOnIdeals Ψ.residue ∧ Ψ.IsNonprincipal ∧ f.absNorm ≤ M.absNorm ∧
      (∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then Ψ.residue (Ideal.Quotient.mk f a) else 0) ∧
      (∀ I : primeToModulusIdeals (integralIdealRayModulus M hM),
        Ψ.idealHom (I : FractionalIdealGroup K) = ψ.idealHom (I : FractionalIdealGroup K)) ∧
      ∀ I : Ideal (𝓞 K),
        ψ.allCoefficient I = if IsCoprime I M then Ψ.allCoefficient I else 0 := by
  obtain ⟨f, hf, hMf, Ψ, hprim, hnorm, hmask, hagree⟩ :=
    ψ.exists_primitive_idealCharacter hM
  exact ⟨f, hf, hMf, Ψ, hprim, ψ.primitiveIdeal_isNonprincipal hM f hMf Ψ hagree hnp,
    hnorm, hmask, hagree, ψ.primitiveIdeal_allCoefficient_mask hM f hMf Ψ hagree⟩

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
