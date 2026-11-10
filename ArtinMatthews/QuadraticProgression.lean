module

public import ArtinMatthews.QuadraticProgressionCharacter
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import ArtinMatthews.QuadraticProgressionFactorization
public import ArtinMatthews.QuadraticProgressionModEight
public import ArtinMatthews.QuadraticResidueChoice
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Construction of one rational progression realizing all prescribed quadratic signs. -/

namespace ArtinMatthews

theorem signs_mul_pow {x y : ℤ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1)
    (n : ℕ) : x * y ^ n = 1 ∨ x * y ^ n = -1 := by
  apply sq_eq_one_iff.mp
  have hx2 : x ^ 2 = 1 := sq_eq_one_iff.mpr hx
  have hy2 : y ^ 2 = 1 := sq_eq_one_iff.mpr hy
  rw [mul_pow, ← pow_mul, Nat.mul_comm n 2, pow_mul, hx2, hy2, one_pow, mul_one]

theorem legendre_congr_nat {q a b : ℕ} [Fact q.Prime] (h : a ≡ b [MOD q]) :
    legendreSym q (a : ℤ) = legendreSym q (b : ℤ) := by
  unfold legendreSym
  congr 1
  exact_mod_cast (ZMod.natCast_eq_natCast_iff a b q).mpr h

theorem legendre_reciprocity_via_minus_one {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    legendreSym p (q : ℤ) = legendreSym p (-1) ^ (q / 2) * legendreSym q (p : ℤ) := by
  have hp : p.Prime := Fact.out
  have hminus : legendreSym p (-1) = (-1 : ℤ) ^ (p / 2) := by
    rw [legendreSym.at_neg_one hp2,
      ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp (hp.odd_of_ne_two hp2))]
  rw [legendreSym.quadratic_reciprocity' hq2 hp2, hminus, ← pow_mul,
    Nat.mul_comm (p / 2) (q / 2)]

theorem legendre_matches_reciprocal_target {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) {x y : ℤ} (hy : y = 1 ∨ y = -1)
    (hminus : legendreSym p (-1) = y)
    (hlocal : legendreSym q (p : ℤ) = x * y ^ (q / 2)) :
    legendreSym p (q : ℤ) = x := by
  have hy2 : y ^ 2 = 1 := sq_eq_one_iff.mpr hy
  have hpow : (y ^ (q / 2)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm (q / 2) 2, pow_mul, hy2, one_pow]
  rw [legendre_reciprocity_via_minus_one hp2 hq2, hminus, hlocal]
  calc
    y ^ (q / 2) * (x * y ^ (q / 2)) = x * (y ^ (q / 2)) ^ 2 := by ring
    _ = x := by rw [hpow, mul_one]

theorem exists_odd_prime_residue {q : ℕ} [Fact q.Prime] (hq : 2 < q)
    {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ∃ r : ℕ, r < q ∧ r ≠ 0 ∧ (3 < q → r ≠ 1) ∧ legendreSym q (r : ℤ) = s := by
  by_cases hq3 : 3 < q
  · obtain ⟨r, hrq, hr0, hr1, hrs⟩ := exists_legendre_residue_avoiding_zero_one hq3 hs
    exact ⟨r, hrq, hr0, fun _ => hr1, hrs⟩
  · rcases hs with rfl | rfl
    · exact ⟨1, by omega, by decide, by omega, by simp⟩
    · have hchar : ringChar (ZMod q) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
      obtain ⟨u, hu⟩ := quadraticChar_exists_neg_one (F := ZMod q) hchar
      refine ⟨u.val, u.val_lt, ?_, by omega, ?_⟩
      · intro hzero
        have hu0 : u = 0 := by rw [← ZMod.natCast_zmod_val u, hzero, Nat.cast_zero]
        rw [hu0, quadraticChar_zero] at hu
        norm_num at hu
      · simpa only [legendreSym, Int.cast_natCast, ZMod.natCast_zmod_val] using hu

/-- A unit residue class simultaneously realizes a square-class character at
minus one, two, and every prime in a prescribed finite odd-prime set. -/
theorem exists_prime_sign_progression (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q)
    (f : RationalSquareClass →ₗ[ZMod 2] ZMod 2) :
    ∃ u : ℕ, u < 8 * ∏ q ∈ Q, q ∧ Nat.Coprime u (8 * ∏ q ∈ Q, q) ∧
      ∀ (p : ℕ) [Fact p.Prime], p ≡ u [MOD 8 * ∏ q ∈ Q, q] →
        p ≠ 2 ∧ legendreSym p (-1) = squareClassCharacter f (-1) ∧
        legendreSym p 2 = squareClassCharacter f 2 ∧
        ∀ q ∈ Q, legendreSym p (q : ℤ) = squareClassCharacter f (q : ℤ) ∧
          (3 < q → p % q ≠ 1) := by
  classical
  let χ := squareClassCharacter f
  have hminus : χ (-1) = 1 ∨ χ (-1) = -1 :=
    squareClassCharacter_cases f (-1) (by norm_num)
  have htwo : χ 2 = 1 ∨ χ 2 = -1 := squareClassCharacter_cases f 2 (by norm_num)
  obtain ⟨r8, _, hr8odd, hr8⟩ := exists_mod_eight_sign_choice hminus htwo
  have hlocal (q : ℕ) (hq : q ∈ Q) :
      ∃ r : ℕ, r < q ∧ r ≠ 0 ∧ (3 < q → r ≠ 1) ∧
        @legendreSym q ⟨(hQ q hq).1⟩ (r : ℤ) = χ (q : ℤ) * χ (-1) ^ (q / 2) := by
    let : Fact q.Prime := ⟨(hQ q hq).1⟩
    apply exists_odd_prime_residue (hQ q hq).2
    apply signs_mul_pow _ hminus
    exact squareClassCharacter_cases f (q : ℤ) (by exact_mod_cast (hQ q hq).1.ne_zero)
  choose r hr using hlocal
  let residue : ℕ → ℕ := fun q => if hq : q ∈ Q then r q hq else 0
  have hres (q : ℕ) (hq : q ∈ Q) :
      residue q < q ∧ residue q ≠ 0 ∧ (3 < q → residue q ≠ 1) ∧
        @legendreSym q ⟨(hQ q hq).1⟩ (residue q : ℤ) =
          χ (q : ℤ) * χ (-1) ^ (q / 2) := by
    simpa only [residue, dite_eq_left hq] using hr q hq
  obtain ⟨u, huBound, hu8, huQ⟩ := exists_common_residue_mod_eight Q hQ residue r8
  have huOdd : Odd u := by
    have hmod := Nat.ModEq.of_dvd (by decide : 2 ∣ 8) hu8
    have hrmod := Nat.odd_iff.mp hr8odd
    have heq : u % 2 = r8 % 2 := hmod
    exact Nat.odd_iff.mpr (heq.trans hrmod)
  have hu8cop : Nat.Coprime u 8 := by
    have h := huOdd.coprime_two_right
    have hh := (Nat.coprime_pow_right_iff (by norm_num : 0 < 3) u 2).mpr h
    simpa using hh
  have huQcop : Nat.Coprime u (∏ q ∈ Q, q) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    apply Nat.Coprime.symm
    apply (hQ q hq).1.coprime_iff_not_dvd.mpr
    intro hdiv
    have hmod := huQ q hq
    change u % q = residue q % q at hmod
    rw [Nat.mod_eq_zero_of_dvd hdiv, Nat.mod_eq_of_lt (hres q hq).1] at hmod
    exact (hres q hq).2.1 hmod.symm
  refine ⟨u, huBound, hu8cop.mul_right huQcop, ?_⟩
  intro p hp hpu
  have hp8 : p ≡ r8 [MOD 8] :=
    (Nat.ModEq.of_dvd (dvd_mul_right 8 _) hpu).trans hu8
  obtain ⟨hp2, hpminus, hptwo⟩ := hr8 p hp8
  refine ⟨hp2, hpminus, hptwo, ?_⟩
  intro q hq
  let : Fact q.Prime := ⟨(hQ q hq).1⟩
  have hq2 : q ≠ 2 := by have := (hQ q hq).2; omega
  have hqp : q ∣ 8 * ∏ q ∈ Q, q :=
    (Finset.dvd_prod_of_mem (fun q : ℕ => q) hq).trans (dvd_mul_left _ _)
  have hpq : p ≡ residue q [MOD q] := (Nat.ModEq.of_dvd hqp hpu).trans (huQ q hq)
  constructor
  · apply legendre_matches_reciprocal_target hp2 hq2 hminus hpminus
    exact (legendre_congr_nat hpq).trans (hres q hq).2.2.2
  · intro hq3 hpeq
    have hmod : p % q = residue q % q := hpq
    rw [Nat.mod_eq_of_lt (hres q hq).1] at hmod
    exact (hres q hq).2.2.1 hq3 (hmod.symm.trans hpeq)

/-- The odd primes used by the quadratic progression, including three. -/
def quadraticPrimeSupport (S : Finset ℤ) : Finset ℕ :=
  insert 3 ((∏ a ∈ S, a.natAbs).primeFactors.erase 2)

/-- The modulus `8` times the product of the selected odd primes. -/
def quadraticModulus (S : Finset ℤ) : ℕ := 8 * ∏ q ∈ quadraticPrimeSupport S, q

theorem quadraticPrimeSupport_prime {S : Finset ℤ} {q : ℕ}
    (hq : q ∈ quadraticPrimeSupport S) : q.Prime ∧ 2 < q := by
  rcases Finset.mem_insert.mp hq with rfl | hq
  · exact ⟨Nat.prime_three, by decide⟩
  · obtain ⟨hq2, hmem⟩ := Finset.mem_erase.mp hq
    have hprime := Nat.prime_of_mem_primeFactors hmem
    exact ⟨hprime, by have := hprime.two_le; omega⟩

theorem prime_divisor_mem_quadraticPrimeSupport {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0) {a : ℤ} (ha : a ∈ S) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqa : q ∣ a.natAbs) :
    q ∈ quadraticPrimeSupport S := by
  have hprod : (∏ a ∈ S, a.natAbs) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    exact Int.natAbs_ne_zero.mpr (hzero b hb)
  apply Finset.mem_insert_of_mem
  apply Finset.mem_erase.mpr
  refine ⟨hq2, Nat.mem_primeFactors.mpr ⟨hq, ?_, hprod⟩⟩
  exact hqa.trans (Finset.dvd_prod_of_mem (fun a : ℤ => a.natAbs) ha)

/-- A progression realizes the square-class functional on every chosen base,
not just its prime factors. -/
theorem exists_quadratic_progression_for_functional {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0) (f : RationalSquareClass →ₗ[ZMod 2] ZMod 2) :
    ∃ u : ℕ, u < quadraticModulus S ∧ Nat.Coprime u (quadraticModulus S) ∧
      ∀ (p : ℕ) [Fact p.Prime], p ≡ u [MOD quadraticModulus S] →
        p ≠ 2 ∧ (∀ a ∈ S, legendreSym p a = squareClassCharacter f a) ∧
        legendreSym p (-3) = squareClassCharacter f (-3) ∧
        ∀ q ∈ quadraticPrimeSupport S, 3 < q → p % q ≠ 1 := by
  obtain ⟨u, hu, hucop, hup⟩ := exists_prime_sign_progression
    (quadraticPrimeSupport S) (fun _ hq => quadraticPrimeSupport_prime hq) f
  refine ⟨u, hu, hucop, ?_⟩
  intro p hp hpu
  obtain ⟨hp2, hminus, htwo, hprimes⟩ := hup p hpu
  refine ⟨hp2, ?_, ?_, fun q hq => (hprimes q hq).2⟩
  · intro a ha
    apply int_hom_eq_of_prime_divisors (legendreSym.hom p) (squareClassCharacter f) a hminus
    intro q hq hqa
    by_cases hq2 : q = 2
    · simpa [hq2] using htwo
    · exact (hprimes q (prime_divisor_mem_quadraticPrimeSupport hzero ha hq hq2 hqa)).1
  · apply int_hom_eq_of_prime_divisors (legendreSym.hom p) (squareClassCharacter f) (-3) hminus
    intro q hq hqa
    have hq3 : q = 3 := by
      apply (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp
      simpa using hqa
    subst q
    exact (hprimes 3 (Finset.mem_insert_self _ _)).1

/-- Failure of obstruction (A) produces the full quadratic progression of
Section 10.1, including avoidance of `1` at every relevant prime above three. -/
theorem exists_quadratic_progression {S : Finset ℤ} (hS : AdmissibleBases S)
    (hA : ¬ ObstructionA S) :
    ∃ u : ℕ, u < quadraticModulus S ∧ Nat.Coprime u (quadraticModulus S) ∧
      ∀ (p : ℕ) [Fact p.Prime], p ≡ u [MOD quadraticModulus S] →
        p ≠ 2 ∧ (∀ a ∈ S, legendreSym p a = -1) ∧
        ∀ q ∈ quadraticPrimeSupport S, 3 < q → p % q ≠ 1 := by
  obtain ⟨f, hf⟩ := exists_squareClassFunctional hS hA
  obtain ⟨u, hu, hcop, hp⟩ := exists_quadratic_progression_for_functional
    (fun a ha => (hS.2 a ha).1) f
  refine ⟨u, hu, hcop, ?_⟩
  intro p hprime hpu
  obtain ⟨hp2, hbase, _, havoid⟩ := hp p hpu
  refine ⟨hp2, ?_, havoid⟩
  intro a ha
  rw [hbase a ha]
  exact squareClassCharacter_eq_neg_one_on_bases (fun a ha => (hS.2 a ha).1) f hf a ha

end ArtinMatthews
