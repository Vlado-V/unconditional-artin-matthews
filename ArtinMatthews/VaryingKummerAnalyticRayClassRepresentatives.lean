module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealCoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine coprime integral representatives of every ideal class.
The generic Dedekind-domain CRT/ideal-product proof is extracted unchanged
from PrincipalUnits, before its signature-specific analytic sections. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField FractionalIdeal Set
open scoped NumberField nonZeroDivisors Classical BigOperators

theorem exists_simultaneous_ideal_generator {R : Type*} [CommRing R]
    [IsDedekindDomain R] (I : Ideal R) (hI : I ≠ ⊥)
    (s : Finset (Ideal R)) (hprime : ∀ P ∈ s, Prime P) :
    ∃ x ∈ I, ∀ P ∈ s, x ∉ P * I := by
  classical
  have hex : ∀ P : s, ∃ x ∈ I, x ∉ P.val * I := by
    intro P
    have hP : P.val ≠ 1 := (hprime P P.property).ne_one
    have hne : P.val * I ≠ I := by
      intro H
      apply hP
      exact mul_right_cancel₀ hI (H.trans (one_mul I).symm)
    have hnle : ¬ I ≤ P.val * I := fun H => hne (le_antisymm Ideal.mul_le_right H)
    exact Set.not_subset.mp hnle
  choose x hx hnx using hex
  have he : ∀ P : s, ∃ e : R, ∀ Q : s,
      e - (if Q = P then 1 else 0) ∈ Q.val := by
    intro P
    obtain ⟨e,he⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (fun Q : Ideal R => Q)
      (fun _ => 1) hprime (by intros; assumption)
      (fun Q : s => if Q = P then (1:R) else 0)
    exact ⟨e, fun Q => by simpa using he Q Q.property⟩
  choose e he using he
  refine ⟨∑ P : s, e P * x P, I.sum_mem (fun P _ => I.mul_mem_left _ (hx P)), ?_⟩
  intro Q hQ hmem
  let q : s := ⟨Q,hQ⟩
  have H : (∑ P : s, e P * x P) - x q ∈ Q * I := by
    have Hsum : (∑ P : s, (e P - if q = P then 1 else 0) * x P) ∈ Q * I :=
      (Q * I).sum_mem fun P _ => Ideal.mul_mem_mul (he P q) (hx P)
    convert Hsum using 1
    simp only [sub_mul, Finset.sum_sub_distrib]
    simp
  exact hnx q ((Q * I).sub_mem hmem H |> fun H' => by simpa using H')

lemma exists_nonzero_simultaneous_ideal_generator {R : Type*} [CommRing R]
    [IsDedekindDomain R] (I : Ideal R) (hI : I ≠ ⊥)
    (s : Finset (Ideal R)) (hprime : ∀ P ∈ s, Prime P) :
    ∃ x ∈ I, x ≠ 0 ∧ ∀ P ∈ s, x ∉ P * I := by
  classical
  obtain rfl | hs := s.eq_empty_or_nonempty
  · obtain ⟨x,hx,hx0⟩ := I.ne_bot_iff.mp hI
    exact ⟨x,hx,hx0, by simp⟩
  · obtain ⟨x,hx,H⟩ := exists_simultaneous_ideal_generator I hI s hprime
    refine ⟨x,hx,?_,H⟩
    obtain ⟨P,hP⟩ := hs
    rintro rfl
    exact H P hP (Ideal.zero_mem _)

 

theorem exists_coprime_ideal_product {R : Type*} [CommRing R]
    [IsDedekindDomain R] (I M : Ideal R) (hI : I ≠ ⊥) (hM : M ≠ ⊥) :
    ∃ (x : R) (J : Ideal R), x ≠ 0 ∧ x ∈ I ∧ J ≠ ⊥ ∧
      IsCoprime J M ∧ Ideal.span {x} = I * J := by
  classical
  obtain ⟨x,hx,hx0,Hx⟩ := exists_nonzero_simultaneous_ideal_generator I hI
    (UniqueFactorizationMonoid.factors M).toFinset
    (fun P hP => UniqueFactorizationMonoid.prime_of_factor P
      (Multiset.mem_toFinset.mp hP))
  obtain ⟨J,hJ⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hx)
  have hJ0 : J ≠ ⊥ := by
    intro H
    rw [H, Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ
    exact hx0 hJ
  refine ⟨x,J,hx0,hx,hJ0,?_,hJ⟩
  apply Ideal.coprime_of_no_prime_ge
  intro P hJP hMP hP
  have hP0 : P ≠ ⊥ := ne_bot_of_le_ne_bot hM hMP
  obtain ⟨Q,hQ,heq⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hM
    (Ideal.prime_of_isPrime hP0 hP).irreducible (Ideal.dvd_iff_le.mpr hMP)
  have HPQ : P = Q := associated_iff_eq.mp heq
  subst Q
  apply Hx P (Multiset.mem_toFinset.mpr hQ)
  have hle : Ideal.span {x} ≤ P * I := by
    rw [hJ, mul_comm I J]
    simpa only [mul_comm I J, mul_comm I P] using mul_le_mul_right hJP I
  exact hle (Ideal.subset_span (by simp))

open scoped nonZeroDivisors in
 

theorem exists_coprime_class_representative {R : Type*} [CommRing R]
    [IsDedekindDomain R] (M : Ideal R) (hM : M ≠ ⊥) (c : ClassGroup R) :
    ∃ J : (Ideal R)⁰, IsCoprime J.val M ∧ ClassGroup.mk0 J = c := by
  obtain ⟨I,hI⟩ := ClassGroup.mk0_surjective c⁻¹
  obtain ⟨x,J,hx0,hx,hJ0,hcop,hprod⟩ := exists_coprime_ideal_product I.val M
    (mem_nonZeroDivisors_iff_ne_zero.mp I.property) hM
  let Jn : (Ideal R)⁰ := ⟨J,mem_nonZeroDivisors_iff_ne_zero.mpr hJ0⟩
  refine ⟨Jn,hcop,?_⟩
  have H : ClassGroup.mk0 I * ClassGroup.mk0 Jn = 1 := by
    rw [← map_mul]
    apply (ClassGroup.mk0_eq_one_iff (I * Jn).property).mpr
    change (I.val * J).IsPrincipal
    rw [← hprod]
    infer_instance
  rw [hI] at H
  have He := congrArg (fun z : ClassGroup R => c * z) H
  simpa only [← mul_assoc,mul_inv_cancel,one_mul,mul_one] using He


variable {K : Type*} [Field K] [NumberField K]

def coprimeClassRepresentative (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (c : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  (exists_coprime_class_representative M hM c).choose

lemma coprimeClassRepresentative_spec (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (c : ClassGroup (𝓞 K)) :
    IsCoprime (coprimeClassRepresentative M hM c).val M ∧
      ClassGroup.mk0 (coprimeClassRepresentative M hM c) = c :=
  (exists_coprime_class_representative M hM c).choose_spec

 


theorem rationalModulusIdeal_ne_bot (N : ℕ) [NeZero N] :
    rationalModulusIdeal (𝓞 K) N ≠ ⊥ := by
  change Ideal.span {(N : 𝓞 K)} ≠ ⊥
  simpa only [ne_eq, Ideal.span_singleton_eq_bot] using
    (Nat.cast_ne_zero.mpr (NeZero.ne N) : (N : 𝓞 K) ≠ 0)

variable (K) (N : ℕ) [NeZero N]

def rayClassRepresentative (c : ClassGroup (𝓞 K)) : Ideal (𝓞 K) :=
  (coprimeClassRepresentative (rationalModulusIdeal (𝓞 K) N)
    (rationalModulusIdeal_ne_bot N) c).val

theorem rayClassRepresentative_ne_bot (c : ClassGroup (𝓞 K)) :
    rayClassRepresentative K N c ≠ ⊥ :=
  mem_nonZeroDivisors_iff_ne_zero.mp
    (coprimeClassRepresentative (rationalModulusIdeal (𝓞 K) N)
      (rationalModulusIdeal_ne_bot N) c).property

theorem rayClassRepresentative_coprime (c : ClassGroup (𝓞 K)) :
    IsCoprime (rayClassRepresentative K N c) (rationalModulusIdeal (𝓞 K) N) :=
  (coprimeClassRepresentative_spec (rationalModulusIdeal (𝓞 K) N)
    (rationalModulusIdeal_ne_bot N) c).1

def rayClassFractionalRepresentative (c : ClassGroup (𝓞 K)) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  integralIdealFractionalUnit (rayClassRepresentative K N c) (rayClassRepresentative_ne_bot K N c)

theorem rayClassFractionalRepresentative_spec (c : ClassGroup (𝓞 K)) :
    ClassGroup.mk K (rayClassFractionalRepresentative K N c) = c := by
  change ClassGroup.mk K (FractionalIdeal.mk0 K
    (coprimeClassRepresentative (rationalModulusIdeal (𝓞 K) N)
      (rationalModulusIdeal_ne_bot N) c)) = c
  rw [ClassGroup.mk_mk0]
  exact (coprimeClassRepresentative_spec (rationalModulusIdeal (𝓞 K) N)
    (rationalModulusIdeal_ne_bot N) c).2

theorem exists_coprime_integral_class_representative (c : ClassGroup (𝓞 K)) :
    ∃ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥), IsCoprime I (rationalModulusIdeal (𝓞 K) N) ∧
      ClassGroup.mk K (integralIdealFractionalUnit I hI) = c :=
  ⟨rayClassRepresentative K N c, rayClassRepresentative_ne_bot K N c,
    rayClassRepresentative_coprime K N c, rayClassFractionalRepresentative_spec K N c⟩

end
end ArtinMatthews.VaryingKummerAnalytic

