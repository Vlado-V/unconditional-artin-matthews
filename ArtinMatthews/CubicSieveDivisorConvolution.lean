module

public import ArtinMatthews.CubicSieveDivisorShift
public import ArtinMatthews.RoughBonferroniDivisors


set_option backward.privateInPublic true
@[expose] public section

/-! The divisor-weight Euler factor of (7.7) as an exact finite convolution.
The subset of repeated primes accounts for the signed second shift. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

def cubicSieveDivisorEulerCoeff (P T : Finset ℕ) : ℝ :=
  ∏ p ∈ P, if p ∈ T then (-1 : ℝ) else 2

private theorem cubicSieveEulerCoeff_insert_notMem {P T : Finset ℕ} {p : ℕ}
    (hp : p ∉ P) (ht : p ∉ T) :
    cubicSieveDivisorEulerCoeff (insert p P) T = 2 * cubicSieveDivisorEulerCoeff P T := by
  simp only [cubicSieveDivisorEulerCoeff, prod_insert hp, ite_eq_right ht]

private theorem cubicSieveEulerCoeff_insert_mem {P T : Finset ℕ} {p : ℕ}
    (hp : p ∉ P) :
    cubicSieveDivisorEulerCoeff (insert p P) (insert p T) =
      -cubicSieveDivisorEulerCoeff P T := by
  rw [cubicSieveDivisorEulerCoeff, prod_insert hp, ite_eq_left (mem_insert_self _ _), neg_one_mul]
  congr 1
  unfold cubicSieveDivisorEulerCoeff
  apply prod_congr rfl
  intro t ht
  simp only [mem_insert, or_iff_right (show t ≠ p from fun h => hp (h ▸ ht))]

theorem cubicSieve_divisorCount_subset_shift (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (if roughSubsetDivisor P ∣ n then (n.divisors.card : ℝ) else 0) =
      ∑ T ∈ P.powerset, cubicSieveDivisorEulerCoeff P T *
        cubicSieveDivisorShift (roughSubsetDivisor P * roughSubsetDivisor T)
          (fun t => (t.divisors.card : ℝ)) n := by
  classical
  induction P using Finset.induction_on generalizing n with
  | empty =>
    simp [roughSubsetDivisor, cubicSieveDivisorEulerCoeff, cubicSieveDivisorShift]
  | @insert p P hp ih =>
    have hpp := hprime p (mem_insert_self _ _)
    have hP (t : ℕ) (ht : t ∈ P) := hprime t (mem_insert_of_mem ht)
    let d := roughSubsetDivisor P
    have hd : 0 < d := roughSubsetDivisor_pos P hP
    have hc : p.Coprime d := by
      apply hpp.coprime_iff_not_dvd.mpr
      intro h
      have hh : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, h, hd.ne'⟩
      unfold d roughSubsetDivisor at hh
      rw [Nat.primeFactors_prod hP] at hh
      exact hp hh
    have hD : roughSubsetDivisor (insert p P) = p * d := prod_insert hp
    have hCop : d.Coprime (p * p) := hc.symm.mul_right hc.symm
    have hsplit : (p * d) ∣ n ↔ p ∣ n ∧ d ∣ n :=
      ⟨fun h => ⟨(dvd_mul_right _ _).trans h, (dvd_mul_left _ _).trans h⟩,
        fun h => hc.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
    let τ : ℕ → ℝ := fun t => (t.divisors.card : ℝ)
    have hgate :
        (if p * d ∣ n then τ n else 0) =
          2 * cubicSieveDivisorShift p (fun t => if d ∣ t then τ t else 0) n -
            cubicSieveDivisorShift (p * p) (fun t => if d ∣ t then τ t else 0) n := by
      rw [← cubicSieve_divisorShift_gate d p hc.symm,
        ← cubicSieve_divisorShift_gate d (p * p) hCop]
      simp only [hsplit]
      have hstep : (if p ∣ n then τ n else 0) =
          2 * cubicSieveDivisorShift p τ n - cubicSieveDivisorShift (p * p) τ n :=
        cubicSieve_divisorCount_prime_shift hpp n
      by_cases hh : d ∣ n
      · simpa only [hh, and_true, ite_true] using hstep
      · simp only [hh, and_false, ite_false, mul_zero, sub_zero]
    have hF : (fun t => if d ∣ t then τ t else 0) =
        fun t => ∑ T ∈ P.powerset, cubicSieveDivisorEulerCoeff P T *
          cubicSieveDivisorShift (d * roughSubsetDivisor T) τ t :=
      funext (ih hP)
    have ht (T : Finset ℕ) (hT : T ∈ P.powerset) : p ∉ T :=
      notMem_of_mem_powerset_of_notMem hT hp
    have hdis : Disjoint P.powerset (P.powerset.image (insert p)) := by
      refine disjoint_left.mpr ?_
      intro T hT h
      obtain ⟨U, _, rfl⟩ := mem_image.mp h
      exact ht _ hT (mem_insert_self _ _)
    have hinj : Set.InjOn (insert p) (P.powerset : Set (Finset ℕ)) := by
      intro T hT U hU h
      have hT' := ht T hT
      have hU' := ht U hU
      simpa only [erase_insert hT', erase_insert hU'] using congrArg (fun V => V.erase p) h
    rw [hD, hgate, hF, cubicSieve_divisorShift_sum _ _ hpp.pos,
      cubicSieve_divisorShift_sum _ _ (Nat.mul_pos hpp.pos hpp.pos),
      powerset_insert, sum_union hdis, sum_image hinj, mul_sum, sub_eq_add_neg,
      ← sum_neg_distrib]
    congr 1
    · apply sum_congr rfl
      intro T hT
      rw [cubicSieveEulerCoeff_insert_notMem hp (ht T hT), mul_assoc,
        mul_assoc p d (roughSubsetDivisor T)]
    · apply sum_congr rfl
      intro T hT
      have hT' : roughSubsetDivisor (insert p T) = p * roughSubsetDivisor T :=
        prod_insert (ht T hT)
      rw [cubicSieveEulerCoeff_insert_mem hp, hT', neg_mul]
      rw [show (p * d) * (p * roughSubsetDivisor T) =
        (p * p) * (d * roughSubsetDivisor T) by ac_rfl]

theorem cubicSieve_divisorCount_squarefree_shift {r : ℕ} (hr : Squarefree r) (n : ℕ) :
    (if r ∣ n then (n.divisors.card : ℝ) else 0) =
      ∑ T ∈ r.primeFactors.powerset, cubicSieveDivisorEulerCoeff r.primeFactors T *
        cubicSieveDivisorShift (r * roughSubsetDivisor T)
          (fun t => (t.divisors.card : ℝ)) n := by
  have hprod : roughSubsetDivisor r.primeFactors = r :=
    Nat.prod_primeFactors_of_squarefree hr
  simpa only [hprod] using
    cubicSieve_divisorCount_subset_shift r.primeFactors
      (fun _ hp => Nat.prime_of_mem_primeFactors hp) n

end ArtinMatthews
