module

public import ArtinMatthews.ProbeAngularCrossCancellation


set_option backward.privateInPublic true
@[expose] public section

/-! Source-field specialization: the primitive twelfth root constructs
both the Eisenstein algebra and the actual sextic roots. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain KummerTheory GlobalClassFieldTheory.Reciprocity
open ArtinMatthews.AngularLambda
open scoped NumberField BigOperators Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K] {ζ : K}

omit [NumberField K] in
theorem probeCyclotomicSexticRoots (hζ : IsPrimitiveRoot ζ 12) : (primitiveRoots 6 K).Nonempty := by
  refine ⟨ζ ^ 2, (mem_primitiveRoots (by decide : 0 < 6)).mpr ?_⟩
  simpa using hζ.pow_of_dvd (p := 2) (by decide) (by decide)

theorem probeCyclotomicAngularResidue_reciprocity (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ P, (6 : 𝓞 K) ∈ P.asIdeal → P ∈ S)
    (B : Subgroup Kˣ)
    (hB : ProbeHilbertSIsotropic K probeSix (by norm_num) (probeCyclotomicSexticRoots hζ) S B)
    (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q) (hP : P ∉ S) (hQ : Q ∉ S)
    (a : ProbeIntegralExteriorGenerator K S B P) (b : ProbeIntegralExteriorGenerator K S B Q) :
    cyclotomicAngularResidueCharacter hζ P (fun h => hP (hS P h)) (Ideal.Quotient.mk P.asIdeal b.value) =
      cyclotomicAngularResidueCharacter hζ Q (fun h => hQ (hS Q h)) (Ideal.Quotient.mk Q.asIdeal a.value) := by
  let : Algebra BaseField K := baseAlgebraOfTwelve hζ
  exact probeAngularResidue_reciprocity K (probeCyclotomicSexticRoots hζ) S hS B hB P Q hPQ hP hQ a b

theorem probeCyclotomicAngularCross_pair_cancel (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ P, (6 : 𝓞 K) ∈ P.asIdeal → P ∈ S)
    (B : Subgroup Kˣ)
    (hB : ProbeHilbertSIsotropic K probeSix (by norm_num) (probeCyclotomicSexticRoots hζ) S B)
    (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q) (hP : P ∉ S) (hQ : Q ∉ S)
    (a : ProbeIntegralExteriorGenerator K S B P) (b : ProbeIntegralExteriorGenerator K S B Q)
    (e l e' l' k k' : ℤ) :
    let z := cyclotomicAngularResidueCharacter hζ P (fun h => hP (hS P h))
      (Ideal.Quotient.mk P.asIdeal b.value)
    let z' := cyclotomicAngularResidueCharacter hζ Q (fun h => hQ (hS Q h))
      (Ideal.Quotient.mk Q.asIdeal a.value)
    z ^ ((e + 3*l) * k' + (e + 3*l-k) * (e' + 3*l')) *
      z' ^ ((e' + 3*l') * k + (e' + 3*l'-k') * (e + 3*l)) *
      (z^2 * z'^2) ^ (e * e') = 1 := by
  let : Algebra BaseField K := baseAlgebraOfTwelve hζ
  have h := probeAngularCross_pair_cancel K (probeCyclotomicSexticRoots hζ) S hS B hB
    P Q hPQ hP hQ a b e l e' l' k k'
  have hv := congrArg (fun u : ℂˣ => (u : ℂ)) h
  simpa only [cyclotomicAngularResidueCharacter, probeAngularCrossUnit, Units.val_mul,
    Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_one, MulChar.coe_toUnitHom,
    AlgebraicNumberTheory.PowerResidueSymbols.primeIdealResidueUnit, Units.val_mk0] using hv

end
end ArtinMatthews.VaryingKummerAnalytic
