module

public import ArtinMatthews.SourcePoissonOriginalPeriod
public import ArtinMatthews.SourcePoissonActualSixthInvariance


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SourcePhysical MeasureTheory
open VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
local notation "S" => sourceHilbertSet F S₀
local notation "Q" => SNormOneSixthQuotient F S
local notation "π" => sNormOneSixthQuotientMap F S

theorem sourcePoissonOriginalDensity_mul_sixth
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (u : SUnitGroup (K := F) S) (t : SNormOne F S) (X Y Z : ℝ) :
    sourcePoissonOriginalDensity F S₀ hζ η hBad X Y Z (t * sNormOneSixthMap F S u) =
      sourcePoissonOriginalDensity F S₀ hζ η hBad X Y Z t :=
  sourcePoissonOriginalDensity_mul_sixth_of_gauss F S₀ hζ η hBad u t X Y Z
    (fun s m => sourcePoissonOriginalGauss_mul_sixth F S₀ hζ s
      (sourcePoissonPrimalUnit F S₀ u) m)

theorem sourcePoissonOriginalDensity_eq_of_quotient
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (X Y Z : ℝ) {u t : SNormOne F S} (he : π u = π t) :
    sourcePoissonOriginalDensity F S₀ hζ η hBad X Y Z u =
      sourcePoissonOriginalDensity F S₀ hζ η hBad X Y Z t := by
  have hq : π (t⁻¹ * u) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
  have hmem : t⁻¹ * u ∈ sNormOneSixthSubgroup F S :=
    (QuotientGroup.eq_one_iff _).mp hq
  obtain ⟨w, hw⟩ := hmem
  have hu : t * sNormOneSixthMap F S w = u := by
    rw [hw, ← mul_assoc, mul_inv_cancel, one_mul]
  exact hu ▸ sourcePoissonOriginalDensity_mul_sixth F S₀ hζ η hBad w t X Y Z

/-- The original density as a representative-independent function on the
literal quotient used in the paper. -/
def sourcePoissonOriginalQuotientDensity
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (X Y Z : ℝ) (q : Q) : ℂ :=
  sourcePoissonOriginalDensity F S₀ hζ η hBad X Y Z (Quotient.out q)

theorem sourcePoissonOriginalQuotientDensity_mk
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (X Y Z : ℝ) (t : SNormOne F S) :
    sourcePoissonOriginalQuotientDensity F S₀ hζ η hBad X Y Z (π t) =
      sourcePoissonOriginalDensity F S₀ hζ η hBad X Y Z t := by
  have h : π (Quotient.out (π t)) = π t := Quotient.out_eq _
  exact sourcePoissonOriginalDensity_eq_of_quotient F S₀ hζ η hBad X Y Z h

end
end ArtinMatthews.SourceEulerAssembly
