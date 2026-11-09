module

public import ArtinMatthews.SourceFrequencyNormOneAction
public import ArtinMatthews.SLocalFieldNorm
public import ArtinMatthews.SLocalPositiveScaling


set_option backward.privateInPublic true
@[expose] public section

/-! The exact multiplicative S-local argument after frequency
unfolding, with its original source radial norm. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

local notation "S" => sourceHilbertSet F S₀

theorem sourceFieldSNorm_div (T : Finset (HeightOneSpectrum (𝓞 F))) (a b : Fˣ) :
    fieldSNorm F T (a / b) = fieldSNorm F T a / fieldSNorm F T b := by
  change sLocalNorm F T (sWholeDiagonal F T (a / b)) = _
  rw [map_div, sLocalNorm_div]
  rfl

theorem sourceAllowedPrimeUnit_fieldSNorm (P : SourceExteriorPrime F S₀) :
    fieldSNorm F S (sourceAllowedPrimeUnit F hζ S₀ P) = Ideal.absNorm P.val.asIdeal :=
  fieldSNorm_exterior_prime_generator F (sourceHilbertSeed F S₀) P.val P.property
    (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)

theorem sourcePrimeExponentUnit_fieldSNorm (e : SourcePrimeExponents F S₀) :
    fieldSNorm F S (sourcePrimeExponentUnit F hζ S₀ e) = sourcePrimeExponentNorm F S₀ e := by
  unfold sourcePrimeExponentUnit sourcePrimeExponentNorm Finsupp.prod
  rw [map_prod, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro P _
  rw [map_pow, sourceAllowedPrimeUnit_fieldSNorm F hζ S₀ P, Nat.cast_pow]

theorem sourceFrequencyRepresentative_fieldUnit (u : SourceFrequencyRepresentativeIndex F S₀) :
    sourceNonzeroFrequencyFieldUnit F S₀ (sourceFrequencyRepresentative F hζ S₀ u) =
      (sourceExteriorUnitSixthRepresentative S u.2).val * sourcePrimeExponentUnit F hζ S₀ u.1.val := by
  apply Units.ext
  rw [sourceNonzeroFrequencyFieldUnit_val, sourceFrequencyRepresentative, sourceFrequencyMonomial_val,
    Subalgebra.coe_mul, sourceExteriorUnitToSourceRing_val, Units.val_mul, sourcePrimeExponentUnit_val]

theorem sourceFrequencyRepresentative_fieldSNorm (u : SourceFrequencyRepresentativeIndex F S₀) :
    fieldSNorm F S (sourceNonzeroFrequencyFieldUnit F S₀ (sourceFrequencyRepresentative F hζ S₀ u)) =
      sourceFrequencyRepresentativeNorm F S₀ u := by
  rw [sourceFrequencyRepresentative_fieldUnit, map_mul, sourcePrimeExponentUnit_fieldSNorm F hζ S₀]
  have hu : fieldSNorm F S (sourceExteriorUnitSixthRepresentative S u.2).val = 1 :=
    fieldSNorm_sUnit F S (SourcePhysical.sourceExteriorUnitToActualSUnit F S
      (sourceExteriorUnitSixthRepresentative S u.2))
  rw [hu, one_mul]
  rfl

def sourceFrequencyPoissonArgument (X : ℝ) (s A : SourcePrimeExponents F S₀)
    (u : SourceFrequencyRepresentativeIndex F S₀) (r : SourcePrimeExponents F S₀) : SWholeUnits F S :=
  sLocalPositiveScaling F hζ S ((sourcePrimeExponentNorm F S₀ s : ℝ) * X) *
    sWholeDiagonal F S
      ((sourceNonzeroFrequencyFieldUnit F S₀ (sourceFrequencyRepresentative F hζ S₀ u) *
        (sourcePrimeExponentUnit F hζ S₀ r) ^ 6) /
        (sourcePrimeExponentUnit F hζ S₀ s * sourcePrimeExponentUnit F hζ S₀ A))

theorem sourceFrequencyPoissonArgument_norm (X : ℝ) (hX : 0 < X)
    (s A : SourcePrimeExponents F S₀) (u : SourceFrequencyRepresentativeIndex F S₀)
    (r : SourcePrimeExponents F S₀) :
    sLocalNorm F S (sourceFrequencyPoissonArgument F hζ S₀ X s A u r) =
      X * (sourceFrequencyRepresentativeNorm F S₀ u : ℝ) *
        (sourcePrimeExponentNorm F S₀ r : ℝ) ^ 6 / (sourcePrimeExponentNorm F S₀ A : ℝ) := by
  have hs : 0 < (sourcePrimeExponentNorm F S₀ s : ℝ) := Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ s)
  have hA : 0 < (sourcePrimeExponentNorm F S₀ A : ℝ) := Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ A)
  rw [sourceFrequencyPoissonArgument, sLocalNorm_mul, sLocalPositiveScaling_norm F hζ S (mul_pos hs hX)]
  change (sourcePrimeExponentNorm F S₀ s : ℝ) * X * fieldSNorm F S
      ((sourceNonzeroFrequencyFieldUnit F S₀ (sourceFrequencyRepresentative F hζ S₀ u) *
        (sourcePrimeExponentUnit F hζ S₀ r) ^ 6) /
        (sourcePrimeExponentUnit F hζ S₀ s * sourcePrimeExponentUnit F hζ S₀ A)) = _
  rw [sourceFieldSNorm_div, map_mul, map_pow, map_mul, sourceFrequencyRepresentative_fieldSNorm F hζ S₀]
  simp only [sourcePrimeExponentUnit_fieldSNorm F hζ S₀]
  field_simp [hs.ne', hA.ne']

theorem sourceFrequencyOrbitEquiv_fieldUnit (u : SourceFrequencyRepresentativeIndex F S₀)
    (r : SourcePrimeExponents F S₀) (v : SourceExteriorUnitSixthPowers S) :
    sourceNonzeroFrequencyFieldUnit F S₀ (sourceFrequencyOrbitEquiv F hζ S₀ (u, r, v)) =
      sourceNonzeroFrequencyFieldUnit F S₀ (sourceFrequencyRepresentative F hζ S₀ u) *
        sourcePrimeExponentUnit F hζ S₀ r ^ 6 * v.val.val := by
  apply Units.ext
  simp only [sourceNonzeroFrequencyFieldUnit_val, sourceFrequencyOrbitEquiv_val,
    Units.val_mul, Units.val_pow_eq_pow_val, sourcePrimeExponentUnit_val]
  rw [Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_pow, sourceExteriorUnitToSourceRing_val]

theorem sourceFrequencyPoissonArgument_orbit (X : ℝ) (s A : SourcePrimeExponents F S₀)
    (u : SourceFrequencyRepresentativeIndex F S₀) (r : SourcePrimeExponents F S₀)
    (v : SourceExteriorUnitSixthPowers S) :
    sLocalPositiveScaling F hζ S ((sourcePrimeExponentNorm F S₀ s : ℝ) * X) *
        sWholeDiagonal F S
          (sourceNonzeroFrequencyFieldUnit F S₀ (sourceFrequencyOrbitEquiv F hζ S₀ (u, r, v)) /
            (sourcePrimeExponentUnit F hζ S₀ s * sourcePrimeExponentUnit F hζ S₀ A)) =
      (SourcePhysical.sourceExteriorSixthNormOneEquiv F S v).val.val *
        sourceFrequencyPoissonArgument F hζ S₀ X s A u r := by
  rw [sourceFrequencyOrbitEquiv_fieldUnit, SourcePhysical.sourceExteriorSixthNormOneEquiv_val,
    sourceFrequencyPoissonArgument]
  rw [mul_div_right_comm, map_mul]
  ac_rfl

end
end ArtinMatthews
