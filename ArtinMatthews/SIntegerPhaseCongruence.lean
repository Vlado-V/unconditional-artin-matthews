module

public import ArtinMatthews.SIntegerStandardPhase


set_option backward.privateInPublic true
@[expose] public section

/-! Dependent quotient-phase transport along equality of actual
denominators. The nonzero proofs are transported by equality induction. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.StandardAdelic
open scoped NumberField
variable {K : Type} [Field K] [NumberField K]

theorem sourcePhase_primitive_congr (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (a b : PrincipalIntegerRing S₀) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a = b) :
    (sIntegerQuotientPhase K (principalizingSet S₀) a ha).IsPrimitive ↔
      (sIntegerQuotientPhase K (principalizingSet S₀) b hb).IsPrimitive := by
  subst b
  rfl

end ArtinMatthews.SIntegerFourier
