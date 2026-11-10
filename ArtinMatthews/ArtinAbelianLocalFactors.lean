module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import ArtinMatthews.ArtinAbelianInertiaCharacters
public import ArtinMatthews.ArtinAbelianLocalEuler


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine abelian Artin local factors indexed by the fixed global character
family. All ramified factors are retained through actual inertia. -/

noncomputable section
namespace ArtinMatthews.AbelianLocal
open scoped NumberField IsMulCommutative Classical BigOperators

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [IsAbelianGalois F E]

/-- An actual choice of a prime ideal above the given base prime. -/
def abelianPrimeAbove (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    Ideal.primesOver P.asIdeal (𝓞 E) := Classical.choice inferInstance

instance abelianPrimeAbove_isMaximal (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    (abelianPrimeAbove F E P).val.IsMaximal :=
  (abelianPrimeAbove F E P).property.1.isMaximal
    (Ideal.ne_bot_of_mem_primesOver P.ne_bot (abelianPrimeAbove F E P).property)

instance abelianPrimeAbove_liesOver (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    (abelianPrimeAbove F E P).val.LiesOver P.asIdeal :=
  (abelianPrimeAbove F E P).property.2

/-- The actual arithmetic Frobenius associated to the chosen prime above P. -/
def abelianPrimeFrobenius (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : Gal(E/F) :=
  arithFrobAt (𝓞 F) Gal(E/F) (abelianPrimeAbove F E P).val

theorem abelianPrimeFrobenius_spec (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    IsArithFrobAt (𝓞 F) (abelianPrimeFrobenius F E P) (abelianPrimeAbove F E P).val :=
  IsArithFrobAt.arithFrobAt (𝓞 F) Gal(E/F) (abelianPrimeAbove F E P).val

/-- The one-dimensional local Artin factor: a ramified character has zero
inertia-fixed space, hence contributes exactly one. -/
def abelianArtinLocalFactor (χ : Gal(E/F) →* ℂˣ)
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ :=
  if (abelianPrimeAbove F E P).val.inertia Gal(E/F) ≤ χ.ker then
    (1 - (χ (abelianPrimeFrobenius F E P) : ℂ) * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹
  else 1

local instance globalCharacterFintype : Fintype (Gal(E/F) →* ℂˣ) := Fintype.ofFinite _
local instance localPrimeFiberFintype (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    Fintype (Ideal.primesOver P.asIdeal (𝓞 E)) := Fintype.ofFinite _

/-- Exact local Dedekind/Artin factorization at every prime, expressed using
one fixed global character family. No unramifiedness or zeta factorization
is supplied as a hypothesis. -/
theorem prod_abelianArtinLocalFactor
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (s : ℂ) :
    (∏ χ : Gal(E/F) →* ℂˣ, abelianArtinLocalFactor F E χ P s) =
      ∏ Q : Ideal.primesOver P.asIdeal (𝓞 E),
        (1 - (Ideal.absNorm Q.val : ℂ) ^ (-s))⁻¹ := by
  change (∏ χ : Gal(E/F) →* ℂˣ,
    if (abelianPrimeAbove F E P).val.inertia Gal(E/F) ≤ χ.ker then
      (1 - (χ (abelianPrimeFrobenius F E P) : ℂ) * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹
    else 1) = _
  rw [prod_all_characters_inertia_factor]
  exact abelian_artin_localEuler F E P (abelianPrimeAbove F E P).val
    (abelianPrimeFrobenius F E P) (abelianPrimeFrobenius_spec F E P) s

end ArtinMatthews.AbelianLocal
