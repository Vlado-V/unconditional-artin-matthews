module

public import ArtinMatthews.SourcePrimeExponentProducts
public import ArtinMatthews.SLocalWeakApproximation
public import ArtinMatthews.SLocalPowerModule


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite S-local square classes of fixed exterior generators.
Equality of classes forces the product generator to be a square at
every place of S. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators ClassFieldTheory
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "S" => sourceHilbertSet F S₀

def sourceQuadraticLocalClass (e : E) : SLocalPowerClasses F 2 S :=
  sLocalGlobalClassMap F 2 S (sourcePrimeExponentUnit F hζ S₀ e)

theorem sourceQuadraticLocalClass_zero : sourceQuadraticLocalClass F S₀ hζ 0 = 1 := by
  rw [sourceQuadraticLocalClass, sourcePrimeExponentUnit_zero, map_one]

theorem sourceQuadraticLocalClass_add (e f : E) :
    sourceQuadraticLocalClass F S₀ hζ (e + f) =
      sourceQuadraticLocalClass F S₀ hζ e * sourceQuadraticLocalClass F S₀ hζ f := by
  rw [sourceQuadraticLocalClass, sourcePrimeExponentUnit_add, map_mul]
  rfl

theorem sourceQuadraticLocalClass_product_one (e f : E)
    (hclass : sourceQuadraticLocalClass F S₀ hζ e = sourceQuadraticLocalClass F S₀ hζ f) :
    sourceQuadraticLocalClass F S₀ hζ (e + f) = 1 := by
  rw [sourceQuadraticLocalClass_add, hclass, ← pow_two]
  exact sLocalPowerClasses_pow_eq_one F 2 S _

theorem sourceQuadraticLocalClass_eq_localSquare (e f : E)
    (hclass : sourceQuadraticLocalClass F S₀ hζ e = sourceQuadraticLocalClass F S₀ hζ f)
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∈ S) :
    ∃ s : P.adicCompletion F,
      s ^ 2 = algebraMap F (P.adicCompletion F) (sourcePrimeExponentUnit F hζ S₀ (e + f) : F) := by
  have h := congrFun (sourceQuadraticLocalClass_product_one F S₀ hζ e f hclass) ⟨P, hP⟩
  change powerClass (P.adicCompletion F) 2
    (Units.map (algebraMap F (P.adicCompletion F)).toMonoidHom
      (sourcePrimeExponentUnit F hζ S₀ (e + f))) = 1 at h
  obtain ⟨s, hs⟩ := (QuotientGroup.eq_one_iff _).mp h
  exact ⟨s.val, congrArg Units.val hs⟩

end
end ArtinMatthews.SourceEulerAssembly
