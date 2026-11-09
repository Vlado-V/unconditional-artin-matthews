module

public import ArtinMatthews.SIntegerPrincipalQuotient


set_option backward.privateInPublic true
@[expose] public section

/-! Every nonzero ideal of the actual constructed S-integer ring has
a finite quotient. This follows from the proved exterior ideal
equivalence and the original number-field ideal quotient, not a finite
quotient hypothesis on the localized ring. -/
namespace ArtinMatthews.SIntegerQuotient

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable {K : Type} [Field K] [NumberField K]

theorem principal_ideal_quotient_finite
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (J : Ideal (PrincipalIntegerRing S₀)) (hJ : J ≠ ⊥) :
    Finite ((PrincipalIntegerRing S₀) ⧸ J) := by
  let j : (Ideal (PrincipalIntegerRing S₀))⁰ :=
    ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ⟩
  let I := (principalExteriorIdealEquiv S₀).symm j
  have hI : I.val.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = J :=
    congrArg Subtype.val ((principalExteriorIdealEquiv S₀).apply_symm_apply j)
  let : Finite ((𝓞 K) ⧸ I.val) := Ring.HasFiniteQuotients.finiteQuotient I.property.1
  exact Finite.of_equiv _ ((principalQuotientEquiv S₀ I.val I.property.2).toRingEquiv.trans
    (Ideal.quotEquivOfEq hI)).toEquiv

theorem principal_element_quotient_finite
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (a : PrincipalIntegerRing S₀) (ha : a ≠ 0) :
    Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) :=
  principal_ideal_quotient_finite S₀ _ (Ideal.span_singleton_eq_bot.not.mpr ha)

end
end ArtinMatthews.SIntegerQuotient
