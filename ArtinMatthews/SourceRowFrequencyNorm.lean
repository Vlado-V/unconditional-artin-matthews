module

public import ArtinMatthews.SourceRowIntegralNumerator
public import ArtinMatthews.SIntegerNormIdentification


set_option backward.privateInPublic true
@[expose] public section

/-! The physical S-product norm of the literal frequency equals its
actual exterior ideal norm. The principal quotient and all exterior
orders are attached to the same source S-integer. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain FractionalIdeal AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "R" => sourceRing F S₀
local notation "S" => sourceHilbertSet F S₀

theorem sourceElementExponents_quotient_card (u : R) (hu : u ≠ 0) :
    Nat.card (R ⧸ Ideal.span {u}) = sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu) := by
  let E := sourceElementExponents F S₀ u hu
  let J := sourcePrimeExponentIdeal F S₀ E
  have hJ : J.map (algebraMap (𝓞 F) R) = Ideal.span {u} := sourceElementExponents_ideal F S₀ u hu
  rw [← hJ]
  exact (principal_quotient_card (sourceHilbertSeed F S₀) J
    (sourcePrimeExponentIdeal_exterior F S₀ E).2).trans (sourcePrimeExponentIdeal_norm F S₀ E)

theorem sourceRowFieldNorm_eq_frequencyNorm {ζ : F} (hζ : IsPrimitiveRoot ζ 12) (u : R) (hu : u ≠ 0) :
    fieldSNorm F S (sourceRowFieldUnit F S₀ u hu) =
      (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu) : ℝ) := by
  let I : (Ideal R)⁰ := ⟨Ideal.span {u}, mem_nonZeroDivisors_iff_ne_zero.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hu)⟩
  have hI : toPrincipalIdeal R F (sourceRowFieldUnit F S₀ u hu) = FractionalIdeal.mk0 F I := by
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    change spanSingleton R⁰ (sourceRowFieldUnit F S₀ u hu : F) =
      (Ideal.span {u} : FractionalIdeal R⁰ F)
    rw [coeIdeal_span_singleton]
    rfl
  calc
    _ = idealSNorm F hζ S₀ (FractionalIdeal.mk0 F I) :=
      (idealSNorm_eq_of_generator F hζ S₀ _ _ hI).symm
    _ = (Nat.card (R ⧸ Ideal.span {u}) : ℝ) := idealSNorm_integral_card F hζ S₀ I
    _ = _ := congrArg (fun q : ℕ => (q : ℝ)) (sourceElementExponents_quotient_card F S₀ u hu)

end
end ArtinMatthews.SourceEulerAssembly
