module

public import ArtinMatthews.SourcePrimeExponents


set_option backward.privateInPublic true
@[expose] public section

/-! A literal generator product is unchanged by adjoining absent primes. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

theorem sourcePrimeExponentGenerator_prefix (e : SourcePrimeExponents F S₀)
    (T : Finset (SourceExteriorPrime F S₀)) (he : e.support ⊆ T) :
    sourcePrimeExponentGenerator F hζ S₀ e =
      ∏ P : T, sourceAllowedPrimeGenerator F hζ S₀ P.val ^ e P.val := by
  calc
    _ = ∏ P ∈ T, sourceAllowedPrimeGenerator F hζ S₀ P ^ e P := by
      apply Finset.prod_subset he
      intro P _ hp
      rw [Finsupp.notMem_support_iff.mp hp]
      exact pow_zero _
    _ = _ := (Finset.prod_coe_sort T _).symm

end
end ArtinMatthews
