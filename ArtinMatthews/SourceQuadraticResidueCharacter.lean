module

public import ArtinMatthews.SourceQuadraticHeckeSymbols
public import ArtinMatthews.QuadraticHeckeProductPrimitive
public import ArtinMatthews.ReflectionCoefficientGaussCRT
public import ArtinMatthews.SourceProductPhasePrimitive


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open SIntegerQuotient SourceCRTNormalization StandardAdelic VaryingKummerAnalytic AngularLambda
open OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "T" => sourceHilbertSeed F S₀
local notation "OS" => PrincipalIntegerRing T
local notation "S" => sourceHilbertSet F S₀
local notation "E" => ReflectionSquarefreeExponents F S₀
local notation "a" => (sourceAllowedPrimeGenerator F hζ S₀ : SourceExteriorPrime F S₀ → OS)
local notation "A" => (sourcePrimeExponentGenerator F hζ S₀ : SourcePrimeExponents F S₀ → OS)

private theorem sourceQuadraticCRTModulus_eq (e : E) :
    crtModulus T (fun i : e.val.support => i.val.val) (fun _ => 1) =
      (Ideal.span {A e.val} : Ideal OS) := by
  rw [crtModulus_generator T _ _ (fun i : e.val.support => a i.val)
    (fun i => sourceAllowedPrimeGenerator_ideal F hζ S₀ i.val)]
  exact congrArg (fun b : OS => (Ideal.span {b} : Ideal OS))
    (reflectionSquarefreeGenerator_support F hζ S₀ e).symm

private theorem sourceQuadraticCRT_support_pairwise (e : E) :
    Pairwise fun i j : e.val.support => i.val.val ≠ j.val.val :=
  fun _ _ hij he => hij (Subtype.ext (Subtype.ext he))

def sourceQuadraticCRT (e : E) :
    (OS ⧸ (Ideal.span {A e.val} : Ideal OS)) ≃+* ∀ i : e.val.support, (𝓞 F) ⧸ i.val.val.asIdeal := by
  let p (i : e.val.support) := i.val.val
  let b (i : e.val.support) : OS := a i.val
  let hb (i : e.val.support) := sourceAllowedPrimeGenerator_ideal F hζ S₀ i.val
  let I : Ideal OS := Ideal.span {A e.val}
  let J : Ideal OS := crtModulus T p (fun _ => 1)
  let eu : (OS ⧸ I) ≃+* (OS ⧸ J) := Ideal.quotEquivOfEq (R := OS)
    (sourceQuadraticCRTModulus_eq F S₀ hζ e).symm
  exact (eu.trans (primeCRTEquiv T p (fun _ => 1) (sourceQuadraticCRT_support_pairwise F S₀ e))).trans
    (RingEquiv.piCongrRight (fun i => reflectionLocalPrimeEquiv T (p i) i.val.property (b i) (hb i)))

theorem sourceQuadraticCRT_mk (e : E) (m : OS) (i : e.val.support) :
    sourceQuadraticCRT F S₀ hζ e (Ideal.Quotient.mk (Ideal.span {A e.val} : Ideal OS) m) i =
      generatorResidueEquiv T i.val.val i.val.property (a i.val)
        (sourceAllowedPrimeGenerator_ideal F hζ S₀ i.val)
        (Ideal.Quotient.mk (Ideal.span {a i.val} : Ideal OS) m) := by
  change reflectionLocalPrimeEquiv T i.val.val i.val.property (a i.val)
    (sourceAllowedPrimeGenerator_ideal F hζ S₀ i.val)
    (primeCRTEquiv T (fun j : e.val.support => j.val.val) (fun _ => 1)
      (sourceQuadraticCRT_support_pairwise F S₀ e) (Ideal.Quotient.mk _ m) i) = _
  rw [primeCRTEquiv_mk]
  exact reflectionLocalPrimeEquiv_mk T i.val.val i.val.property (a i.val)
    (sourceAllowedPrimeGenerator_ideal F hζ S₀ i.val) m

def sourceReflectionQuadraticCharacter (e : E) : MulChar (OS ⧸ (Ideal.span {A e.val} : Ideal OS)) ℂ :=
  pullCharacter (sourceQuadraticCRT F S₀ hζ e)
    (reflectionProductCharacter (fun i : e.val.support => (𝓞 F) ⧸ i.val.val.asIdeal)
      (fun i => reflectionPrimeCharacters F hζ S₀ i.val ^ 3))

theorem sourceReflectionQuadraticCharacter_primitive (e : E) :
    IsPrimitiveOnIdeals (sourceReflectionQuadraticCharacter F S₀ hζ e) := by
  let : ∀ i : e.val.support, Field ((𝓞 F) ⧸ i.val.val.asIdeal) := fun i => Ideal.Quotient.field _
  apply primitiveOnIdeals_pullCharacter
  apply reflectionProductCharacter_primitiveOnIdeals
  intro i h
  have hd := orderOf_dvd_iff_pow_eq_one.mpr h
  unfold reflectionPrimeCharacters at hd
  rw [cyclotomicAngularResidueCharacter_order] at hd
  norm_num at hd

set_option backward.isDefEq.respectTransparency false in
theorem sourceReflectionQuadraticCharacter_apply (e : E) (m : OS) :
    sourceReflectionQuadraticCharacter F S₀ hζ e (Ideal.Quotient.mk (Ideal.span {A e.val} : Ideal OS) m) =
      reflectionExponentResidueValue F hζ S₀ e.val m ^ 3 := by
  unfold sourceReflectionQuadraticCharacter
  rw [pullCharacter_apply, reflectionSquarefreeResidueValue_support F hζ S₀ e]
  change (∏ i : e.val.support, (reflectionPrimeCharacters F hζ S₀ i.val ^ 3)
    (sourceQuadraticCRT F S₀ hζ e (Ideal.Quotient.mk (Ideal.span {A e.val} : Ideal OS) m) i)) = _
  unfold sourceSexticWeight crtResidueWeight
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), sourceQuadraticCRT_mk F S₀ hζ]
  have h := reflectionLocalPrimeCharacter_weight T i.val.val i.val.property (a i.val)
    (sourceAllowedPrimeGenerator_ideal F hζ S₀ i.val) (reflectionPrimeCharacters F hζ S₀ i.val)
    (Ideal.Quotient.mk (primePowerIdeal T i.val.val 1) m)
  rw [reflectionLocalPrimeCharacter, pullCharacter_apply, reflectionLocalPrimeEquiv_mk] at h
  exact congrArg (fun z : ℂ => z ^ 3) h

end
end ArtinMatthews.SourceEulerAssembly
