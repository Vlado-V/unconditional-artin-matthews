module

public import ArtinMatthews.SIntegerLocalCZeroValues


set_option backward.privateInPublic true
@[expose] public section

/-! The absent inner modulus is evaluated directly as one residue,
not as a masked zeroth power character on a nontrivial quotient. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def standardLocalAbsent (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k J : ℕ) : ℂ :=
  ∑' d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a * a ^ k},
    if a ^ J - Quotient.out d ∈ Ideal.span {a * a ^ k} then
      generatorResidueCharacter S₀ P hP a ha (χ ^ (k + 1)) (quotientReduction a (a ^ k) d)
    else 0

theorem standardLocalAbsent_eval (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k J : ℕ) :
    standardLocalAbsent S₀ P hP a ha χ k J =
      generatorResidueCharacter S₀ P hP a ha (χ ^ (k + 1))
        (Ideal.Quotient.mk (Ideal.span {a}) (a ^ J)) := by
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a * a ^ k}) :=
    principal_element_quotient_finite S₀ _ (mul_ne_zero (exterior_generator_ne_zero S₀ P a ha)
      (pow_ne_zero k (exterior_generator_ne_zero S₀ P a ha)))
  let : Fintype ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a * a ^ k}) := Fintype.ofFinite _
  have hg (d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a * a ^ k}) :
      a ^ J - Quotient.out d ∈ Ideal.span {a * a ^ k} ↔
        d = Ideal.Quotient.mk (Ideal.span {a * a ^ k}) (a ^ J) := by
    constructor
    · intro hm
      have hh := Ideal.Quotient.eq.mpr hm
      simpa only [Ideal.Quotient.mk_out] using hh.symm
    · intro hd
      apply Ideal.Quotient.eq.mp
      rw [Ideal.Quotient.mk_out, hd]
  unfold standardLocalAbsent
  simp only [tsum_fintype, hg, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

theorem standardLocalAbsent_eq (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k J : ℕ) :
    standardLocalAbsent S₀ P hP a ha χ k J = if J = 0 then 1 else 0 := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  rw [standardLocalAbsent_eval]
  by_cases hJ : J = 0
  · subst J
    rw [ite_eq_left rfl]
    simp only [pow_zero, map_one]
  · rw [ite_eq_right hJ]
    have haQ : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    change (χ ^ (k + 1)) (generatorResidueEquiv S₀ P hP a ha
      (Ideal.Quotient.mk (Ideal.span {a}) (a ^ J))) = 0
    rw [map_pow, haQ, zero_pow hJ, map_zero, MulChar.map_zero]

end
end ArtinMatthews.SIntegerFourier
