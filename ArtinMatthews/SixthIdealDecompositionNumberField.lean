module

public import ArtinMatthews.SixthIdealDecomposition
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical sixth-power ideal decomposition in the actual ring of
integers of an arbitrary number field, with its actual absolute norm.
This concerns ideals only; no S-unit or character parametrization is used. -/
namespace ArtinMatthews
open scoped NumberField
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem sixthIdealDecomposition_absNorm (I : Ideal (𝓞 K)) (hI : I≠0) :
    I.absNorm=(sixthIdealRemainder I).absNorm*(sixthIdealQuotient I).absNorm^6 := by
  have h := congrArg (fun J : Ideal (𝓞 K) => J.absNorm) (sixthIdealDecomposition_eq I hI)
  simpa only [map_mul,map_pow] using h

theorem sixthIdealDecomposition_absNorm_real (I : Ideal (𝓞 K)) (hI : I≠0) :
    (I.absNorm:ℝ)=((sixthIdealRemainder I).absNorm:ℝ)*((sixthIdealQuotient I).absNorm:ℝ)^6 := by
  exact_mod_cast sixthIdealDecomposition_absNorm I hI

theorem sixthIdealDecomposition_norms_pos (I : Ideal (𝓞 K)) :
    0 < (sixthIdealRemainder I).absNorm ∧ 0 < (sixthIdealQuotient I).absNorm := by
  constructor
  · exact Nat.pos_of_ne_zero (fun h => sixthIdealRemainder_ne_zero I (Ideal.absNorm_eq_zero_iff.mp h))
  · exact Nat.pos_of_ne_zero (fun h => sixthIdealQuotient_ne_zero I (Ideal.absNorm_eq_zero_iff.mp h))

/-- Every nonzero integral ideal of the supplied number field has a unique
actual sixth-free remainder and sixth-power quotient, including the exact
absolute norm identity. -/
theorem sixthIdealDecomposition_numberField_existsUnique (I : Ideal (𝓞 K)) (hI : I≠0) :
    ∃! p : Ideal (𝓞 K) × Ideal (𝓞 K),
      p.1≠0 ∧ p.2≠0 ∧ SixthFreeIdeal p.1 ∧ I=p.1*p.2^6 ∧
        I.absNorm=p.1.absNorm*p.2.absNorm^6 := by
  refine ⟨(sixthIdealRemainder I,sixthIdealQuotient I),
    ⟨sixthIdealRemainder_ne_zero I,sixthIdealQuotient_ne_zero I,
      sixthIdealRemainder_sixthFree I,sixthIdealDecomposition_eq I hI,
      sixthIdealDecomposition_absNorm I hI⟩,?_⟩
  intro p hp
  have h := sixthIdealDecomposition_unique hp.1 (sixthIdealRemainder_ne_zero I)
    hp.2.1 (sixthIdealQuotient_ne_zero I) hp.2.2.1 (sixthIdealRemainder_sixthFree I)
    (hp.2.2.2.1.symm.trans (sixthIdealDecomposition_eq I hI))
  exact Prod.ext h.1 h.2

/-- A fixed finite excluded set of prime ideals remains absent from both
canonical factors. The statement is stronger: no primality assumption on
the excluded divisors is needed. -/
theorem sixthIdealDecomposition_numberField_away (I : Ideal (𝓞 K)) (hI : I≠0)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, ¬P ∣ I) :
    I=sixthIdealRemainder I*sixthIdealQuotient I^6 ∧
      sixthIdealRemainder I≠0 ∧ sixthIdealQuotient I≠0 ∧
      SixthFreeIdeal (sixthIdealRemainder I) ∧
      I.absNorm=(sixthIdealRemainder I).absNorm*(sixthIdealQuotient I).absNorm^6 ∧
      (∀ P ∈ S, ¬P ∣ sixthIdealRemainder I) ∧ (∀ P ∈ S, ¬P ∣ sixthIdealQuotient I) := by
  have hs := sixthIdealDecomposition_avoids I hI S hS
  exact ⟨sixthIdealDecomposition_eq I hI,sixthIdealRemainder_ne_zero I,
    sixthIdealQuotient_ne_zero I,sixthIdealRemainder_sixthFree I,
    sixthIdealDecomposition_absNorm I hI,hs.1,hs.2⟩

theorem sixthIdealDecomposition_numberField_existsUnique_away (I : Ideal (𝓞 K)) (hI : I≠0)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, ¬P ∣ I) :
    ∃! p : Ideal (𝓞 K) × Ideal (𝓞 K),
      p.1≠0 ∧ p.2≠0 ∧ SixthFreeIdeal p.1 ∧ I=p.1*p.2^6 ∧
        I.absNorm=p.1.absNorm*p.2.absNorm^6 ∧
        (∀ P ∈ S, ¬P ∣ p.1) ∧ (∀ P ∈ S, ¬P ∣ p.2) := by
  have hs := sixthIdealDecomposition_avoids I hI S hS
  refine ⟨(sixthIdealRemainder I,sixthIdealQuotient I),
    ⟨sixthIdealRemainder_ne_zero I,sixthIdealQuotient_ne_zero I,
      sixthIdealRemainder_sixthFree I,sixthIdealDecomposition_eq I hI,
      sixthIdealDecomposition_absNorm I hI,hs.1,hs.2⟩,?_⟩
  intro p hp
  have h := sixthIdealDecomposition_unique hp.1 (sixthIdealRemainder_ne_zero I)
    hp.2.1 (sixthIdealQuotient_ne_zero I) hp.2.2.1 (sixthIdealRemainder_sixthFree I)
    (hp.2.2.2.1.symm.trans (sixthIdealDecomposition_eq I hI))
  exact Prod.ext h.1 h.2

end
end ArtinMatthews
