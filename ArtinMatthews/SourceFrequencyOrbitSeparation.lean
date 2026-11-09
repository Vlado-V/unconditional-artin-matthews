module

public import ArtinMatthews.SourceFrequencyOrbits


set_option backward.privateInPublic true
@[expose] public section

/-! Distinct actual reduced source rows have distinct global
sixth-power classes. The residual orbit action is by genuine exterior
S-unit sixth powers. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open scoped NumberField Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

def sourceNonzeroFrequencyFieldUnit (x : SourceNonzeroFrequency F S₀) : Fˣ :=
  Units.mk0 (x.val : F) (fun h => x.property (Subtype.ext h))

@[simp] theorem sourceNonzeroFrequencyFieldUnit_val (x : SourceNonzeroFrequency F S₀) :
    (sourceNonzeroFrequencyFieldUnit F S₀ x : F) = (x.val : F) := rfl

theorem sourceFrequencyRepresentative_reduced (u : SourceFrequencyRepresentativeIndex F S₀) :
    ExteriorSixthReduced (sourceHilbertSet F S₀)
      (sourceNonzeroFrequencyFieldUnit F S₀ (sourceFrequencyRepresentative F hζ S₀ u)) := by
  intro P hP
  let Q : SourceExteriorPrime F S₀ := ⟨P, hP⟩
  have he := sourceElementExponents_valuation F S₀ hζ
    (sourceFrequencyRepresentative F hζ S₀ u).val
    (sourceFrequencyRepresentative F hζ S₀ u).property Q
  rw [sourceFrequencyRepresentative_exponents F hζ S₀ u] at he
  change 0 ≤ exteriorPrincipalValuation Q.val _ ∧ exteriorPrincipalValuation Q.val _ < 6
  rw [sourceExteriorPrincipalValuation_eq_neg_log, sourceNonzeroFrequencyFieldUnit_val, he,
    WithZero.log_exp, neg_neg]
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast u.1.property Q⟩

theorem sourceFrequencyOrbitEquiv_zero_exterior (u : SourceFrequencyRepresentativeIndex F S₀)
    (v : SourceExteriorUnitSixthPowers (sourceHilbertSet F S₀)) :
    (sourceFrequencyOrbitEquiv F hζ S₀ (u, 0, v)).val =
      (sourceFrequencyRepresentative F hζ S₀ u).val * sourceExteriorUnitToSourceRing F S₀ v.val := by
  rw [sourceFrequencyOrbitEquiv_val, sourcePrimeExponentGenerator_zero, one_pow, mul_one]

theorem sourceFrequencyRepresentative_ratio_unit_sixth_implies_eq
    (u v : SourceFrequencyRepresentativeIndex F S₀) (t : Fˣ)
    (ht : sourceNonzeroFrequencyFieldUnit F S₀ (sourceFrequencyRepresentative F hζ S₀ u) /
      sourceNonzeroFrequencyFieldUnit F S₀ (sourceFrequencyRepresentative F hζ S₀ v) = t ^ 6) :
    u = v := by
  let S := sourceHilbertSet F S₀
  let a := sourceFrequencyRepresentative F hζ S₀ u
  let b := sourceFrequencyRepresentative F hζ S₀ v
  let A := sourceNonzeroFrequencyFieldUnit F S₀ a
  let B := sourceNonzeroFrequencyFieldUnit F S₀ b
  have htS : t ∈ exteriorUnitSubgroup S :=
    (exteriorSixthReduced_ratio_root S A B t (sourceFrequencyRepresentative_reduced F hζ S₀ u)
      (sourceFrequencyRepresentative_reduced F hζ S₀ v) ht).2
  let s : exteriorUnitSubgroup S := ⟨t, htS⟩
  let w : SourceExteriorUnitSixthPowers S := ⟨s ^ 6, ⟨s, rfl⟩⟩
  have he := congrArg (fun x : Fˣ => (x : F)) ht
  rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val] at he
  have hfield : (a.val : F) = (b.val : F) * (t : F) ^ 6 := by
    change (a.val : F) / (b.val : F) = (t : F) ^ 6 at he
    rw [mul_comm]
    exact (div_eq_iff (show (b.val : F) ≠ 0 from B.ne_zero)).mp he
  have horbit : sourceFrequencyOrbitEquiv F hζ S₀ (u, 0, 1) =
      sourceFrequencyOrbitEquiv F hζ S₀ (v, 0, w) := by
    apply Subtype.ext
    rw [sourceFrequencyOrbitEquiv_zero_exterior, sourceFrequencyOrbitEquiv_zero_exterior]
    change a.val * sourceExteriorUnitToSourceRing F S₀ 1 =
      b.val * sourceExteriorUnitToSourceRing F S₀ (s ^ 6)
    rw [map_one, mul_one]
    apply Subtype.ext
    rw [Subalgebra.coe_mul, sourceExteriorUnitToSourceRing_val]
    simpa only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, s] using hfield
  exact congrArg Prod.fst ((sourceFrequencyOrbitEquiv F hζ S₀).injective horbit)

theorem sourceFrequencyRepresentative_ratio_sixth_implies_eq
    (u v : SourceFrequencyRepresentativeIndex F S₀)
    (ht : ∃ t : F, (((sourceFrequencyRepresentative F hζ S₀ u).val : F) /
      ((sourceFrequencyRepresentative F hζ S₀ v).val : F)) = t ^ 6) :
    u = v := by
  obtain ⟨t, ht⟩ := ht
  let A := sourceNonzeroFrequencyFieldUnit F S₀ (sourceFrequencyRepresentative F hζ S₀ u)
  let B := sourceNonzeroFrequencyFieldUnit F S₀ (sourceFrequencyRepresentative F hζ S₀ v)
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by decide : 6 ≠ 0)] at ht
    exact div_ne_zero A.ne_zero B.ne_zero ht
  apply sourceFrequencyRepresentative_ratio_unit_sixth_implies_eq F hζ S₀ u v (Units.mk0 t ht0)
  apply Units.ext
  rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, Units.val_mk0]
  exact ht

end
end ArtinMatthews
