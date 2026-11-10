module

public import ArtinMatthews.PrimeExtractionTupleRecursion
public import ArtinMatthews.CubicThetaCoefficients
public import ArtinMatthews.QuadraticIdealNormCountGlobal
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.Radical.NatInt
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


set_option backward.privateInPublic true
@[expose] public section

/-! Support and factorial bounds for the actual second coefficient beta_j. -/

namespace ArtinMatthews

open OAI.SevenEighths
open scoped BigOperators

theorem prime_extraction_list_product_norm_le (a : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (l : List ℕ) (hl : ∀ p ∈ l, ‖a p‖ ≤ C) : ‖(l.map a).prod‖ ≤ C ^ l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, norm_mul, List.length_cons, pow_succ']
    exact mul_le_mul (hl p List.mem_cons_self)
      (ih (fun q hq => hl q (List.mem_cons_of_mem p hq))) (norm_nonneg _) hC

theorem roughPrimeTupleCoefficient_norm_le (a : ℕ → ℂ) (j n : ℕ) (z : ℝ)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ p : ℕ, p.Prime → z < (p : ℝ) → ‖a p‖ ≤ C) :
    ‖roughPrimeTupleCoefficient a j n z‖ ≤ (j.factorial : ℝ) * C ^ j := by
  calc
    _ ≤ ∑ l ∈ roughOrderedPrimeFactorizations j n z, ‖(l.map a).prod‖ := norm_sum_le _ _
    _ ≤ ∑ _l ∈ roughOrderedPrimeFactorizations j n z, C ^ j := by
      apply Finset.sum_le_sum
      intro l hl
      obtain ⟨hlen, _, hp⟩ := (mem_roughOrderedPrimeFactorizations j n z l).mp hl
      simpa only [hlen] using prime_extraction_list_product_norm_le a hC l
        (fun p hpl => ha p (hp p hpl).1 (hp p hpl).2)
    _ = ((roughOrderedPrimeFactorizations j n z).card : ℝ) * C ^ j := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (roughOrderedPrimeFactorizations_card_le j n z)) (pow_nonneg hC _)

/-- A nonzero beta coefficient is supported on actual rough integers with
exactly j prime factors, counted with multiplicity. -/
theorem roughPrimeTupleCoefficient_support (a : ℕ → ℂ) (j n : ℕ) (z : ℝ)
    (ha : roughPrimeTupleCoefficient a j n z ≠ 0) :
    n ≠ 0 ∧ MarkedRoughAbove z n ∧ n.primeFactorsList.length = j := by
  obtain ⟨l, hl, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  have hn := roughOrderedPrimeFactorizations_nonzero hl
  obtain ⟨hlen, hprod, hp⟩ := (mem_roughOrderedPrimeFactorizations j n z l).mp hl
  have hperm := Nat.primeFactorsList_unique hprod (fun p hpl => (hp p hpl).1)
  refine ⟨hn, ?_, hperm.length_eq.symm.trans hlen⟩
  intro p hprime hpd
  exact (hp p (hperm.mem_iff.mpr ((Nat.mem_primeFactorsList hn).mpr ⟨hprime, hpd⟩))).2

theorem idealThetaCoeff_prime_norm_le_two (η : HeckeFamily.Character) {p : ℕ} (hp : p.Prime) :
    ‖idealThetaCoeff η p‖ ≤ 2 := by
  have h := idealThetaCoeff_norm_le_divisors_card η p
  simpa only [hp.divisors, Finset.card_pair hp.ne_one.symm, Nat.cast_ofNat] using h

/-- The actual beta_j from Proposition 8.1, with repeated prime factors
temporarily allowed, has the required bound 2^j*j! without assumptions
about the coefficients or the prime distribution. -/
theorem roughThetaTupleCoefficient_norm_le (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (j n : ℕ) (z : ℝ) :
    ‖roughPrimeTupleCoefficient (fun p => idealThetaCoeff η p * χ p) j n z‖ ≤
      (j.factorial : ℝ) * (2 : ℝ) ^ j := by
  apply roughPrimeTupleCoefficient_norm_le _ _ _ _ (by norm_num)
  intro p hp _
  calc
    _ = ‖idealThetaCoeff η p‖ * ‖χ p‖ := norm_mul _ _
    _ ≤ 2 * 1 := mul_le_mul (idealThetaCoeff_prime_norm_le_two η hp)
      (χ.norm_le_one _) (norm_nonneg _) (by norm_num)
    _ = 2 := by ring

end ArtinMatthews
