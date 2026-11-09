module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas


set_option backward.privateInPublic true
@[expose] public section

/-! Canonical sixth-power decomposition in the actual monoid of integral
ideals of a Dedekind domain. The construction divides each normalized
prime-factor multiplicity by six; no decomposition is an input. -/
namespace ArtinMatthews
open UniqueFactorizationMonoid
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

def sixthIdealValuation (I P : Ideal R) : ℕ := (normalizedFactors I).count P

def sixthIdealFactorMultiset (I : Ideal R) (e : ℕ → ℕ) : Multiset (Ideal R) :=
  ∑ P ∈ (normalizedFactors I).toFinset, Multiset.replicate (e (sixthIdealValuation I P)) P

theorem sixthIdealFactorMultiset_subset (I : Ideal R) (e : ℕ → ℕ) :
    sixthIdealFactorMultiset I e ⊆ normalizedFactors I := by
  intro P hP
  obtain ⟨Q,hQ,hPQ⟩ := Multiset.mem_sum.mp hP
  have he : P=Q := (Multiset.mem_replicate.mp hPQ).2
  exact he ▸ Multiset.mem_toFinset.mp hQ

theorem sixthIdealFactorMultiset_count (I P : Ideal R) (e : ℕ → ℕ) (he : e 0=0) :
    (sixthIdealFactorMultiset I e).count P=e (sixthIdealValuation I P) := by
  unfold sixthIdealFactorMultiset
  simp only [Multiset.count_sum',Multiset.count_replicate,Finset.sum_ite_eq']
  split_ifs with hP
  · rfl
  · have hz : sixthIdealValuation I P=0 := Multiset.count_eq_zero.mpr
      (fun h => hP (Multiset.mem_toFinset.mpr h))
    rw [hz,he]

def sixthIdealFactorPart (I : Ideal R) (e : ℕ → ℕ) : Ideal R :=
  (sixthIdealFactorMultiset I e).prod

theorem sixthIdealFactorPart_ne_zero (I : Ideal R) (e : ℕ → ℕ) :
    sixthIdealFactorPart I e ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (sixthIdealFactorMultiset_subset I e)

theorem sixthIdealFactorPart_valuation (I P : Ideal R) (e : ℕ → ℕ) (he : e 0=0) :
    sixthIdealValuation (sixthIdealFactorPart I e) P=e (sixthIdealValuation I P) := by
  unfold sixthIdealValuation sixthIdealFactorPart
  rw [normalizedFactors_prod_eq_self_of_subset (sixthIdealFactorMultiset_subset I e)]
  exact sixthIdealFactorMultiset_count I P e he

theorem sixthIdealFactorPart_factors_subset (I : Ideal R) (e : ℕ → ℕ) :
    normalizedFactors (sixthIdealFactorPart I e) ⊆ normalizedFactors I := by
  unfold sixthIdealFactorPart
  rw [normalizedFactors_prod_eq_self_of_subset (sixthIdealFactorMultiset_subset I e)]
  exact sixthIdealFactorMultiset_subset I e

def sixthIdealRemainder (I : Ideal R) : Ideal R := sixthIdealFactorPart I (fun n => n % 6)

def sixthIdealQuotient (I : Ideal R) : Ideal R := sixthIdealFactorPart I (fun n => n / 6)

def SixthFreeIdeal (I : Ideal R) : Prop := ∀ P, sixthIdealValuation I P < 6

theorem sixthIdealRemainder_ne_zero (I : Ideal R) : sixthIdealRemainder I ≠ 0 :=
  sixthIdealFactorPart_ne_zero I _

theorem sixthIdealQuotient_ne_zero (I : Ideal R) : sixthIdealQuotient I ≠ 0 :=
  sixthIdealFactorPart_ne_zero I _

@[simp] theorem sixthIdealRemainder_valuation (I P : Ideal R) :
    sixthIdealValuation (sixthIdealRemainder I) P=sixthIdealValuation I P % 6 :=
  sixthIdealFactorPart_valuation I P _ (by decide)

@[simp] theorem sixthIdealQuotient_valuation (I P : Ideal R) :
    sixthIdealValuation (sixthIdealQuotient I) P=sixthIdealValuation I P / 6 :=
  sixthIdealFactorPart_valuation I P _ (by decide)

theorem sixthIdealValuation_mul (I J P : Ideal R) (hI : I≠0) (hJ : J≠0) :
    sixthIdealValuation (I*J) P=sixthIdealValuation I P+sixthIdealValuation J P := by
  simp only [sixthIdealValuation,normalizedFactors_mul hI hJ,Multiset.count_add]

theorem sixthIdealValuation_pow (I P : Ideal R) (n : ℕ) :
    sixthIdealValuation (I^n) P=n*sixthIdealValuation I P := by
  simp only [sixthIdealValuation,normalizedFactors_pow,Multiset.count_nsmul]

theorem sixthIdeal_eq_of_valuation_eq {I J : Ideal R} (hI : I≠0) (hJ : J≠0)
    (h : ∀ P, sixthIdealValuation I P=sixthIdealValuation J P) : I=J := by
  rw [← Ideal.prod_normalizedFactors_eq_self hI,← Ideal.prod_normalizedFactors_eq_self hJ]
  exact congrArg Multiset.prod (Multiset.ext.mpr h)

theorem sixthIdealDecomposition_eq (I : Ideal R) (hI : I≠0) :
    I=sixthIdealRemainder I*sixthIdealQuotient I^6 := by
  symm
  apply sixthIdeal_eq_of_valuation_eq
    (mul_ne_zero (sixthIdealRemainder_ne_zero I) (pow_ne_zero _ (sixthIdealQuotient_ne_zero I))) hI
  intro P
  rw [sixthIdealValuation_mul _ _ _ (sixthIdealRemainder_ne_zero I)
    (pow_ne_zero _ (sixthIdealQuotient_ne_zero I)),sixthIdealValuation_pow,
    sixthIdealRemainder_valuation,sixthIdealQuotient_valuation]
  omega

theorem sixthIdealRemainder_sixthFree (I : Ideal R) : SixthFreeIdeal (sixthIdealRemainder I) := by
  intro P
  rw [sixthIdealRemainder_valuation]
  omega

/-- Equality of two actual sixth-power products determines both factors;
all prime multiplicities of the remainders are strictly below six. -/
theorem sixthIdealDecomposition_unique {U V A B : Ideal R}
    (hU : U≠0) (hV : V≠0) (hA : A≠0) (hB : B≠0)
    (hUf : SixthFreeIdeal U) (hVf : SixthFreeIdeal V)
    (he : U*A^6=V*B^6) : U=V ∧ A=B := by
  have hv (P : Ideal R) := congrArg (fun I => sixthIdealValuation I P) he
  simp only [sixthIdealValuation_mul _ _ _ hU (pow_ne_zero _ hA),
    sixthIdealValuation_mul _ _ _ hV (pow_ne_zero _ hB),sixthIdealValuation_pow] at hv
  have hc (P : Ideal R) : sixthIdealValuation U P=sixthIdealValuation V P ∧
      sixthIdealValuation A P=sixthIdealValuation B P := by
    have := hv P
    have := hUf P
    have := hVf P
    omega
  exact ⟨sixthIdeal_eq_of_valuation_eq hU hV (fun P => (hc P).1),
    sixthIdeal_eq_of_valuation_eq hA hB (fun P => (hc P).2)⟩

theorem sixthIdealDecomposition_existsUnique (I : Ideal R) (hI : I≠0) :
    ∃! p : Ideal R × Ideal R, p.1≠0 ∧ p.2≠0 ∧ SixthFreeIdeal p.1 ∧ I=p.1*p.2^6 := by
  refine ⟨(sixthIdealRemainder I,sixthIdealQuotient I),
    ⟨sixthIdealRemainder_ne_zero I,sixthIdealQuotient_ne_zero I,
      sixthIdealRemainder_sixthFree I,sixthIdealDecomposition_eq I hI⟩,?_⟩
  intro p hp
  have h := sixthIdealDecomposition_unique hp.1 (sixthIdealRemainder_ne_zero I)
    hp.2.1 (sixthIdealQuotient_ne_zero I) hp.2.2.1 (sixthIdealRemainder_sixthFree I)
    (hp.2.2.2.symm.trans (sixthIdealDecomposition_eq I hI))
  exact Prod.ext h.1 h.2

theorem sixthIdealRemainder_dvd (I : Ideal R) (hI : I≠0) : sixthIdealRemainder I ∣ I :=
  ⟨sixthIdealQuotient I^6,sixthIdealDecomposition_eq I hI⟩

theorem sixthIdealQuotient_dvd (I : Ideal R) (hI : I≠0) : sixthIdealQuotient I ∣ I := by
  refine ⟨sixthIdealRemainder I*sixthIdealQuotient I^5,?_⟩
  calc
    I = sixthIdealRemainder I*sixthIdealQuotient I^6 := sixthIdealDecomposition_eq I hI
    _ = sixthIdealQuotient I*(sixthIdealRemainder I*sixthIdealQuotient I^5) := by
      rw [show sixthIdealQuotient I^6=sixthIdealQuotient I^5*sixthIdealQuotient I from pow_succ _ 5]
      ac_rfl

/-- Absence of every ideal divisor in a fixed finite set is preserved in
both canonical factors. In particular this applies to any finite set of
prime ideals removed from the exterior support. -/
theorem sixthIdealDecomposition_avoids (I : Ideal R) (hI : I≠0) (S : Finset (Ideal R))
    (hS : ∀ P ∈ S, ¬P ∣ I) :
    (∀ P ∈ S, ¬P ∣ sixthIdealRemainder I) ∧ (∀ P ∈ S, ¬P ∣ sixthIdealQuotient I) := by
  constructor
  · intro P hP hdiv
    exact hS P hP (hdiv.trans (sixthIdealRemainder_dvd I hI))
  · intro P hP hdiv
    exact hS P hP (hdiv.trans (sixthIdealQuotient_dvd I hI))

def sixthIdealSupport (I : Ideal R) : Finset (Ideal R) := (normalizedFactors I).toFinset

theorem sixthIdealRemainder_support_subset (I : Ideal R) :
    sixthIdealSupport (sixthIdealRemainder I) ⊆ sixthIdealSupport I := by
  intro P hP
  exact Multiset.mem_toFinset.mpr
    (sixthIdealFactorPart_factors_subset I _ (Multiset.mem_toFinset.mp hP))

theorem sixthIdealQuotient_support_subset (I : Ideal R) :
    sixthIdealSupport (sixthIdealQuotient I) ⊆ sixthIdealSupport I := by
  intro P hP
  exact Multiset.mem_toFinset.mpr
    (sixthIdealFactorPart_factors_subset I _ (Multiset.mem_toFinset.mp hP))

theorem sixthIdealDecomposition_support_disjoint (I : Ideal R) (S : Finset (Ideal R))
    (hS : Disjoint S (sixthIdealSupport I)) :
    Disjoint S (sixthIdealSupport (sixthIdealRemainder I)) ∧
      Disjoint S (sixthIdealSupport (sixthIdealQuotient I)) :=
  ⟨hS.mono_right (sixthIdealRemainder_support_subset I),
    hS.mono_right (sixthIdealQuotient_support_subset I)⟩

end
end ArtinMatthews
