module

public import ArtinMatthews.SourcePrimeExponents


set_option backward.privateInPublic true
@[expose] public section

/-! Exact monomial product rules and the literal principal ideal of the fixed generator. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]

theorem sourcePrimeExponentIdeal_zero (S₀ : Finset (HeightOneSpectrum (𝓞 F))) :
    sourcePrimeExponentIdeal F S₀ 0 = 1 := by
  simp [sourcePrimeExponentIdeal]

theorem sourcePrimeExponentIdeal_add (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (e f : SourcePrimeExponents F S₀) :
    sourcePrimeExponentIdeal F S₀ (e + f) =
      sourcePrimeExponentIdeal F S₀ e * sourcePrimeExponentIdeal F S₀ f := by
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem sourcePrimeExponentNorm_zero (S₀ : Finset (HeightOneSpectrum (𝓞 F))) :
    sourcePrimeExponentNorm F S₀ 0 = 1 := by
  simp [sourcePrimeExponentNorm]

theorem sourcePrimeExponentNorm_add (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (e f : SourcePrimeExponents F S₀) :
    sourcePrimeExponentNorm F S₀ (e + f) =
      sourcePrimeExponentNorm F S₀ e * sourcePrimeExponentNorm F S₀ f := by
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem sourcePrimeExponentGenerator_zero {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) :
    sourcePrimeExponentGenerator F hζ S₀ 0 = 1 := by
  simp [sourcePrimeExponentGenerator]

theorem sourcePrimeExponentGenerator_add {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (e f : SourcePrimeExponents F S₀) :
    sourcePrimeExponentGenerator F hζ S₀ (e + f) =
      sourcePrimeExponentGenerator F hζ S₀ e * sourcePrimeExponentGenerator F hζ S₀ f := by
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem sourcePrimeExponentUnit_zero {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) :
    sourcePrimeExponentUnit F hζ S₀ 0 = 1 := by
  simp [sourcePrimeExponentUnit]

theorem sourcePrimeExponentUnit_add {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (e f : SourcePrimeExponents F S₀) :
    sourcePrimeExponentUnit F hζ S₀ (e + f) =
      sourcePrimeExponentUnit F hζ S₀ e * sourcePrimeExponentUnit F hζ S₀ f := by
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem sourcePrimeExponentGenerator_ideal {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (e : SourcePrimeExponents F S₀) :
    (sourcePrimeExponentIdeal F S₀ e).map (algebraMap (𝓞 F) (sourceRing F S₀)) =
      Ideal.span {sourcePrimeExponentGenerator F hζ S₀ e} := by
  change (Ideal.mapHom (algebraMap (𝓞 F) (sourceRing F S₀)))
    (∏ P ∈ e.support, P.val.asIdeal ^ e P) = _
  rw [map_prod]
  calc
    _ = ∏ P ∈ e.support, Ideal.span {sourceAllowedPrimeGenerator F hζ S₀ P ^ e P} := by
      apply Finset.prod_congr rfl
      intro P _
      change (P.val.asIdeal ^ e P).map _ = _
      rw [Ideal.map_pow, sourceAllowedPrimeGenerator_ideal F hζ S₀,
        Ideal.span_singleton_pow]
    _ = Ideal.span {sourcePrimeExponentGenerator F hζ S₀ e} :=
      Ideal.prod_span_singleton _ _

end
end ArtinMatthews
