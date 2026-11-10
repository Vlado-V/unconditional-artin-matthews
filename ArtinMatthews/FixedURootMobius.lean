module

public import ArtinMatthews.FixedURootDensity
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Topology.Sheaves.Init
public import OAI.NumberTheory.Jacobsthal.Sieve.MobiusCoprimeExpansion
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-!
# The exact Möbius expansion of the fixed-u density

Only squarefree divisors contribute to the Möbius sum. Their prime supports
identify the sum with the full divisor sum of the radical formed from primes
of `u` not dividing `S`. Its Euler product is the fixed-u root density.
-/

namespace ArtinMatthews

open scoped BigOperators ArithmeticFunction.Moebius

/-- The radical supported on the prime divisors of `u` which do not divide `S`. -/
noncomputable def fixedUAllowedRadical (u S : ℕ) : ℕ :=
  ∏ p ∈ u.primeFactors.filter (fun p => ¬ p ∣ S), p

theorem fixedUAllowedRadical_pos (u S : ℕ) : 0 < fixedUAllowedRadical u S := by
  apply Finset.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

theorem fixedUAllowedRadical_primeFactors (u S : ℕ) :
    (fixedUAllowedRadical u S).primeFactors =
      u.primeFactors.filter (fun p => ¬ p ∣ S) :=
  Nat.primeFactors_prod (fun _ hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)

theorem fixedUAllowedRadical_squarefree (u S : ℕ) : Squarefree (fixedUAllowedRadical u S) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)).mpr hpq
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).squarefree

theorem fixedUAllowedRadical_dvd (u S : ℕ) : fixedUAllowedRadical u S ∣ u := by
  apply dvd_trans (Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p) (Finset.filter_subset _ _))
  exact Nat.prod_primeFactors_dvd u

theorem fixedUAllowedRadical_coprime (u S : ℕ) : (fixedUAllowedRadical u S).Coprime S := by
  rw [fixedUAllowedRadical, Nat.coprime_prod_left_iff]
  intro p hp
  exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).coprime_iff_not_dvd.mpr
    (Finset.mem_filter.mp hp).2

/-- A squarefree divisor avoids `S` exactly when it divides the allowed radical. -/
theorem fixedUAllowedRadical_dvd_iff {u S d : ℕ} (hu : 0 < u) :
    d ∣ fixedUAllowedRadical u S ↔ d ∣ u ∧ Squarefree d ∧ d.Coprime S := by
  constructor
  · intro hd
    exact ⟨hd.trans (fixedUAllowedRadical_dvd u S),
      (fixedUAllowedRadical_squarefree u S).squarefree_of_dvd hd,
      (fixedUAllowedRadical_coprime u S).of_dvd_left hd⟩
  · rintro ⟨hdu, hd, hdS⟩
    rw [← Nat.prod_primeFactors_of_squarefree hd]
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    refine Finset.mem_filter.mpr ⟨Nat.primeFactors_mono hdu hu.ne' hp, ?_⟩
    exact (Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd.mp
      (hdS.of_dvd_left (Nat.dvd_of_mem_primeFactors hp))

theorem fixedUAllowedRadical_divisors {u S : ℕ} (hu : 0 < u) :
    (fixedUAllowedRadical u S).divisors =
      u.divisors.filter (fun d => Squarefree d ∧ d.Coprime S) := by
  ext d
  constructor
  · intro hd
    obtain ⟨hdu, hsq, hcop⟩ := (fixedUAllowedRadical_dvd_iff hu).mp
      (Nat.dvd_of_mem_divisors hd)
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdu, hu.ne'⟩, hsq, hcop⟩
  · intro hd
    obtain ⟨hdu, hsq, hcop⟩ := Finset.mem_filter.mp hd
    exact Nat.mem_divisors.mpr
      ⟨(fixedUAllowedRadical_dvd_iff hu).mpr ⟨Nat.dvd_of_mem_divisors hdu, hsq, hcop⟩,
        (fixedUAllowedRadical_pos u S).ne'⟩

/-- Removing nonsquarefree terms does not change the restricted Möbius sum. -/
theorem fixedU_moebius_restrict_squarefree (u S : ℕ) :
    (∑ d ∈ u.divisors.filter (fun d => d.Coprime S), (μ d : ℝ) / d) =
      ∑ d ∈ u.divisors.filter (fun d => Squarefree d ∧ d.Coprime S), (μ d : ℝ) / d := by
  classical
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hs : Squarefree d
  · simp only [hs, true_and]
  · simp only [hs, false_and, ite_false]
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
    simp

/-- Exact restricted divisor expansion of the Euler product. -/
theorem fixedU_restricted_moebius_eq_product {u S : ℕ} (hu : 0 < u) :
    (∑ d ∈ u.divisors.filter (fun d => d.Coprime S), (μ d : ℝ) / d) =
      ∏ p ∈ u.primeFactors.filter (fun p => ¬ p ∣ S), (1 - (p : ℝ)⁻¹) := by
  rw [fixedU_moebius_restrict_squarefree, ← fixedUAllowedRadical_divisors hu]
  rw [OAI.Erdos970.ErdosCoprimeResidueInterval.moebius_density _ (fixedUAllowedRadical_pos u S)]
  rw [real_totient_eq_mul_primeFactors, fixedUAllowedRadical_primeFactors]
  have hR : (fixedUAllowedRadical u S : ℝ) ≠ 0 := by
    exact_mod_cast (fixedUAllowedRadical_pos u S).ne'
  field_simp

theorem fixedU_primeFactors_filter_gcd {u S : ℕ} :
    u.primeFactors.filter (fun p => ¬ p ∣ Nat.gcd S u) =
      u.primeFactors.filter (fun p => ¬ p ∣ S) := by
  ext p
  by_cases hp : p ∈ u.primeFactors
  · simp only [Finset.mem_filter, hp, true_and, Nat.dvd_gcd_iff,
      Nat.dvd_of_mem_primeFactors hp, and_true]
  · simp only [Finset.mem_filter, hp, false_and]

/-- The fixed-u root density is its exact Möbius divisor sum. This holds for
arbitrary `S`, and in particular for the squarefree residue modulus in PD. -/
theorem fixedURootDensity_eq_moebius_sum {u S : ℕ} (hu : 0 < u) :
    fixedURootDensity u (Nat.gcd S u) =
      ∑ d ∈ u.divisors.filter (fun d => d.Coprime S), (μ d : ℝ) / d := by
  rw [fixedURootDensity_eq_product hu (Nat.gcd_pos_of_pos_right S hu) (Nat.gcd_dvd_right S u),
    fixedU_primeFactors_filter_gcd]
  exact (fixedU_restricted_moebius_eq_product hu).symm

end ArtinMatthews
