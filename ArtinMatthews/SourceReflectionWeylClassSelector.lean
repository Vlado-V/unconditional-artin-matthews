module

public import ArtinMatthews.SourceReflectionClassSelector
public import ArtinMatthews.SourceSLocalWeylClassPhase


set_option backward.privateInPublic true
@[expose] public section

/-! The same reflected row slice fixes the denominator class in the
actual cubic Weyl phase. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "S" => sourceHilbertSet F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "Prime" => SourceExteriorPrime F S₀
local notation "Q" => SWholePowerClasses F 6 S
local notation "Q₃" => SWholePowerClasses F 3 S
local notation "C" => sourceReflectionExponentSixthClass F S₀ hζ
local notation "cl" => sWholeGlobalClassMap F 6 S
local notation "cl₃" => sWholeGlobalClassMap F 3 S
local notation "gen" => sourcePrimeExponentUnit F hζ S₀
local notation "ε" => sourceExteriorUnitSixthRepresentative (F := F) S
local notation "δ" => sourceReflectionClassIndicator F S₀ hζ

abbrev sourceReflectionCubeClassMap : Q →* Q₃ :=
  powerQuotientMapOfDvd (SWholeUnits F S) 6 3 (by decide)

@[simp] theorem sourceReflectionCubeClassMap_global (b : Fˣ) :
    sourceReflectionCubeClassMap F S₀ (cl b) = cl₃ b :=
  rfl

def sourceReflectionDenominatorSixthClass (f : Finset Prime) (sd : Q) : Q :=
  C (sourceReflectionActiveExponents F S₀ f) ^ (-2 : ℤ) * sd ^ (-2 : ℤ)

theorem sourceReflectionDenominatorSixthClass_eq (f : Finset Prime) (d : E) :
    cl ((gen (sourceReflectionActiveExponents F S₀ f + d))⁻¹ ^ 2) =
      sourceReflectionDenominatorSixthClass F S₀ hζ f (C d) := by
  let cf := C (sourceReflectionActiveExponents F S₀ f)
  simp only [map_pow, map_inv]
  change (C (sourceReflectionActiveExponents F S₀ f + d))⁻¹ ^ 2 =
    cf ^ (-2 : ℤ) * C d ^ (-2 : ℤ)
  rw [sourceReflectionExponentSixthClass_add, mul_inv_rev cf (C d),
    mul_pow (C d)⁻¹ cf⁻¹ 2, inv_pow (C d) 2, inv_pow cf 2]
  exact (mul_comm ((C d) ^ 2)⁻¹ (cf ^ 2)⁻¹).trans
    (congrArg₂ (· * ·) (zpow_negSucc cf 1).symm (zpow_negSucc (C d) 1).symm)

theorem sourceReflectionWeylPhase_eq_denominatorClass (f : Finset Prime) (d : E)
    (x : SWholeUnits F S) :
    sourceSLocalWeylPhase F S hζ (gen (sourceReflectionActiveExponents F S₀ f + d)) x =
      sourceSLocalWeylClassPhase F S hζ
        (sourceReflectionCubeClassMap F S₀ (sourceReflectionDenominatorSixthClass F S₀ hζ f (C d)))
        (QuotientGroup.mk' (powMonoidHom 3 : SWholeUnits F S →* SWholeUnits F S).range x) := by
  rw [← sourceReflectionDenominatorSixthClass_eq, sourceReflectionCubeClassMap_global]
  exact sourceSLocalWeylPhase_eq_classPhase F S hζ _ x

/-- The two classes used by the reflected profile and the cubic Weyl
phase are fixed together on each pair of class slices. -/
theorem sourceReflectionProfileWeylClassSelector (u : ExteriorUnitSixthClasses (K := F) S)
    (f : Finset Prime) (a n d c : E) (γ : Fˣ) (Φ : Q → Q₃ → ℂ) :
    (∑ sd ∈ sourceReflectionSixthClassLabels F S₀ hζ,
      ∑ sc ∈ sourceReflectionSixthClassLabels F S₀ hζ,
        δ d sd * δ c sc *
          Φ (sourceReflectionProfileClass F S₀ hζ u f a n sd sc)
            (sourceReflectionCubeClassMap F S₀ (sourceReflectionDenominatorSixthClass F S₀ hζ f sd))) =
    Φ (cl (γ ^ 6 * (ε u).val * gen (a + c + 3 • n) /
      gen (sourceReflectionActiveExponents F S₀ f + d) ^ 2))
      (cl₃ ((gen (sourceReflectionActiveExponents F S₀ f + d))⁻¹ ^ 2)) := by
  rw [sourceReflectionProfileClass_eq, ← sourceReflectionCubeClassMap_global,
    sourceReflectionDenominatorSixthClass_eq]
  exact sourceReflectionClassSelector F S₀ hζ d c
    (fun sd sc => Φ (sourceReflectionProfileClass F S₀ hζ u f a n sd sc)
      (sourceReflectionCubeClassMap F S₀ (sourceReflectionDenominatorSixthClass F S₀ hζ f sd)))

end
end ArtinMatthews.SourceEulerAssembly
