module

public import ArtinMatthews.SIntegerSexticTransport
public import ArtinMatthews.SIntegerPrimeCRT
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.Algebra.Field.Equiv


set_option backward.privateInPublic true
@[expose] public section

/-! An actual exterior S-integer prime unit remains a unit modulo every
prime power. This supplies the quotient units used in the source change
of variables, without requiring a global S-unit. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

theorem sourceGenerator_maximal (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) :
    (Ideal.span {a}).IsMaximal := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  apply Ideal.Quotient.maximal_of_isField
  exact MulEquiv.isField (Field.toIsField ((𝓞 K) ⧸ P.asIdeal))
    (generatorResidueEquiv S₀ P hP a ha).toMulEquiv

theorem sourcePrimePower_isUnit (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (n : ℕ) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    IsUnit (Ideal.Quotient.mk (primePowerIdeal S₀ P n) x) := by
  let : (Ideal.span {a}).IsMaximal := sourceGenerator_maximal S₀ P hP a ha
  have hx' : x ∉ Ideal.span {a} := by rwa [← ha]
  have h := Ideal.Quotient.isUnit_mk_pow_of_notMem (I := Ideal.span {a}) (n := n) hx'
  rw [primePowerIdeal, generator_power_ideal S₀ P a ha n, ← Ideal.span_singleton_pow]
  exact h

def sourcePrimePowerUnit (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (n : ℕ) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ P n)ˣ :=
  (sourcePrimePower_isUnit S₀ P hP a ha n x hx).choose

theorem sourcePrimePowerUnit_val (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (n : ℕ) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    (sourcePrimePowerUnit S₀ P hP a ha n x hx : (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ P n) =
      Ideal.Quotient.mk _ x :=
  (sourcePrimePower_isUnit S₀ P hP a ha n x hx).choose_spec

end
end ArtinMatthews.SourceCRTNormalization
