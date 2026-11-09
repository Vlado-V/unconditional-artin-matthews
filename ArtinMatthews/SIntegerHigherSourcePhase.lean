module

public import ArtinMatthews.SIntegerLocalCOne
public import ArtinMatthews.PrincipalOppositeFourier
public import ArtinMatthews.PrincipalHigherCancellation


set_option backward.privateInPublic true
@[expose] public section

/-! The literal two-factor source phase and its exact lower phase.
Primitivity is derived from the actual exterior prime and codifferent. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def sourceHigherPhase (a : PrincipalIntegerRing S₀) (ha : a ≠ 0) (m n : ℕ) :
    AddChar ((PrincipalIntegerRing S₀) ⧸ Ideal.span {(a * a ^ m) * (a * a ^ n)}) ℂ :=
  sIntegerQuotientPhase K (principalizingSet S₀) ((a * a ^ m) * (a * a ^ n))
    (mul_ne_zero (mul_ne_zero ha (pow_ne_zero m ha)) (mul_ne_zero ha (pow_ne_zero n ha)))

theorem sourceHigherPhase_primitive (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) (m n : ℕ) :
    (sourceHigherPhase S₀ a (exterior_generator_ne_zero S₀ P a ha) m n).IsPrimitive := by
  have he : (a * a ^ m) * (a * a ^ n) = a ^ (m + n + 2) := by
    simp only [pow_add, pow_succ]
    ring
  unfold sourceHigherPhase
  exact (sourcePhase_primitive_congr S₀ _ _ _ _ he).mpr
    (sIntegerQuotientPhase_primitive S₀ P hP a ha (m + n + 2) hbad)

theorem sourceHigherPhase_lower (a : PrincipalIntegerRing S₀) (ha : a ≠ 0) (m n : ℕ) :
    oppositeLowerChar (a * a ^ m) (a * a ^ n) (sourceHigherPhase S₀ a ha m n) =
      linearPowerPhase S₀ a ha n := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [oppositeLowerChar_mk]
  change sIntegerQuotientPhase K (principalizingSet S₀) ((a * a ^ m) * (a * a ^ n)) _
    (Ideal.Quotient.mk _ ((a * a ^ m) * x)) = _
  unfold linearPowerPhase
  rw [sIntegerQuotientPhase_mk, sIntegerQuotientPhase_mk]
  have haK : (a : K) ≠ 0 := fun h => ha (Subtype.ext h)
  congr 1
  change (((a : K) * (a : K)^m) * (x : K)) /
    (((a : K) * (a : K)^m) * ((a : K) * (a : K)^n)) =
      (x : K) / ((a : K) * (a : K)^n)
  field_simp

end
end ArtinMatthews.SIntegerFourier
