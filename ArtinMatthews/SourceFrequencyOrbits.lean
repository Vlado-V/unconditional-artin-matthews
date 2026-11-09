module

public import ArtinMatthews.SourceFrequencyFactorization


set_option backward.privateInPublic true
@[expose] public section

/-! Actual source frequency orbits. Each nonzero S-integer occurs once
as a reduced row, an exterior ideal sixth power, and a distinct S-unit
sixth power. The representative of the principal row is literally one. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open scoped NumberField Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

abbrev SourceFrequencyRepresentativeIndex :=
  SourceReducedFrequencyExponents F S₀ × ExteriorUnitSixthClasses (sourceHilbertSet F S₀)

abbrev SourceFrequencyOrbitIndex :=
  SourceFrequencyRepresentativeIndex F S₀ ×
    (SourcePrimeExponents F S₀ × SourceExteriorUnitSixthPowers (sourceHilbertSet F S₀))

def sourceFrequencyRepresentative (u : SourceFrequencyRepresentativeIndex F S₀) : SourceNonzeroFrequency F S₀ :=
  sourceFrequencyMonomial F hζ S₀ u.1.val
    (sourceExteriorUnitSixthRepresentative (sourceHilbertSet F S₀) u.2)

theorem sourceFrequencyRepresentative_exponents (u : SourceFrequencyRepresentativeIndex F S₀) :
    sourceElementExponents F S₀ (sourceFrequencyRepresentative F hζ S₀ u).val
      (sourceFrequencyRepresentative F hζ S₀ u).property = u.1.val :=
  sourceFrequencyMonomial_exponents F hζ S₀ _ _

theorem sourceFrequencyRepresentative_exponents_lt_six (u : SourceFrequencyRepresentativeIndex F S₀)
    (P : SourceExteriorPrime F S₀) :
    sourceElementExponents F S₀ (sourceFrequencyRepresentative F hζ S₀ u).val
      (sourceFrequencyRepresentative F hζ S₀ u).property P < 6 := by
  rw [sourceFrequencyRepresentative_exponents]
  exact u.1.property P

def sourceFrequencyPrincipalIndex : SourceFrequencyRepresentativeIndex F S₀ :=
  (⟨0, by intro P; simp⟩, 1)

@[simp] theorem sourceFrequencyRepresentative_principal :
    (sourceFrequencyRepresentative F hζ S₀ (sourceFrequencyPrincipalIndex F S₀)).val = 1 := by
  change (sourceFrequencyMonomial F hζ S₀ 0
    (sourceExteriorUnitSixthRepresentative (sourceHilbertSet F S₀) 1)).val = 1
  rw [sourceFrequencyMonomial_val, sourceExteriorUnitSixthRepresentative_one, map_one,
    sourcePrimeExponentGenerator_zero, one_mul]

def sourceFrequencyOrbitEquiv : SourceFrequencyOrbitIndex F S₀ ≃ SourceNonzeroFrequency F S₀ :=
  ((Equiv.prodProdProdComm _ _ _ _).trans
    ((sourceFrequencyExponentSplit F S₀).prodCongr (sourceExteriorUnitSixthEquiv (sourceHilbertSet F S₀)))).trans
      (sourceFrequencyMonomialEquiv F hζ S₀)

theorem sourceFrequencyOrbitEquiv_val (u : SourceFrequencyRepresentativeIndex F S₀)
    (r : SourcePrimeExponents F S₀) (v : SourceExteriorUnitSixthPowers (sourceHilbertSet F S₀)) :
    (sourceFrequencyOrbitEquiv F hζ S₀ (u, r, v)).val =
      (sourceFrequencyRepresentative F hζ S₀ u).val *
        sourcePrimeExponentGenerator F hζ S₀ r ^ 6 * sourceExteriorUnitToSourceRing F S₀ v.val := by
  change (sourceFrequencyMonomial F hζ S₀
    (sourceFrequencyExponentSplit F S₀ (u.1, r))
    (sourceExteriorUnitSixthEquiv (sourceHilbertSet F S₀) (u.2, v))).val = _
  simp only [sourceFrequencyRepresentative, sourceFrequencyMonomial_val, sourceFrequencyExponentSplit_apply,
    sourceExteriorUnitSixthEquiv_apply, map_mul, sourcePrimeExponentGenerator_add,
    sourcePrimeExponentGenerator_nsmul]
  ring

theorem sourceFrequencyOrbitEquiv_exponents (u : SourceFrequencyRepresentativeIndex F S₀)
    (r : SourcePrimeExponents F S₀) (v : SourceExteriorUnitSixthPowers (sourceHilbertSet F S₀)) :
    sourceElementExponents F S₀ (sourceFrequencyOrbitEquiv F hζ S₀ (u, r, v)).val
      (sourceFrequencyOrbitEquiv F hζ S₀ (u, r, v)).property = u.1.val + 6 • r :=
  sourceFrequencyMonomial_exponents F hζ S₀ _ _

end
end ArtinMatthews
