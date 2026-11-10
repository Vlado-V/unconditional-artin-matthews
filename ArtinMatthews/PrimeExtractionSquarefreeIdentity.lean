module

public import ArtinMatthews.CubicThetaCoefficients
public import ArtinMatthews.PrimeExtractionTupleRecursion
public import ArtinMatthews.CubicThetaCoefficientMultiplicative
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact factorial expansion for the genuine squarefree theta coefficient.
The coprime multiplicativity input is discharged by the ideal-norm fiber theorem. -/

namespace ArtinMatthews

open OAI.SevenEighths
open scoped BigOperators

noncomputable def twistedThetaArithmeticFunction (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ where
  toFun n := idealThetaCoeff η n * χ n
  map_zero' := by simp

theorem twistedThetaArithmeticFunction_isMultiplicative (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (twistedThetaArithmeticFunction η χ).IsMultiplicative := by
  constructor
  · simp [twistedThetaArithmeticFunction]
  · intro m n hmn
    change idealThetaCoeff η (m * n) * χ ((m * n : ℕ) : ZMod q) = _
    rw [idealThetaCoeff_mul_of_coprime η hmn, Nat.cast_mul, map_mul]
    change _ = (idealThetaCoeff η m * χ m) * (idealThetaCoeff η n * χ n)
    ring

theorem squarefree_ordered_coefficient_product (a : ArithmeticFunction ℂ)
    (ha : a.IsMultiplicative) {n : ℕ} (hn : Squarefree n)
    {l : List ℕ} (hl : l ∈ orderedPrimeFactorizations n) : (l.map a).prod = a n := by
  have hperm := List.mem_permutations.mp (List.mem_toFinset.mp hl)
  calc
    _ = (n.primeFactorsList.map a).prod := (hperm.map a).prod_eq
    _ = ∏ p ∈ n.primeFactors, a p := by
      simpa only [Nat.toFinset_factors] using
        (List.prod_toFinset a ((Nat.squarefree_iff_nodup_primeFactorsList hn.ne_zero).mp hn)).symm
    _ = a n := ha.prod_primeFactors hn

/-- Every squarefree rough integer with j prime factors occurs exactly j!
times, and every ordered tuple has its genuine coefficient a(n). -/
theorem squarefree_roughPrimeTupleCoefficient (a : ArithmeticFunction ℂ)
    (ha : a.IsMultiplicative) {j n : ℕ} (hn : Squarefree n) {z : ℝ}
    (hrough : MarkedRoughAbove z n) (hj : n.primeFactorsList.length = j) :
    roughPrimeTupleCoefficient a j n z = (j.factorial : ℂ) * a n := by
  unfold roughPrimeTupleCoefficient
  rw [roughOrderedPrimeFactorizations_eq hn.ne_zero hrough hj]
  calc
    _ = ∑ _l ∈ orderedPrimeFactorizations n, a n :=
      Finset.sum_congr rfl (fun _ hl => squarefree_ordered_coefficient_product a ha hn hl)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, orderedPrimeFactorizations_card hn, hj]

/-- The arithmetic factorial identity needed in Proposition 8.1, for the
actual ideal-theta coefficient times any Dirichlet character. -/
theorem squarefree_theta_ordered_factorization (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) {j n : ℕ} (hn : Squarefree n) {z : ℝ}
    (hrough : MarkedRoughAbove z n) (hj : n.primeFactorsList.length = j) :
    idealThetaCoeff η n * χ n =
      roughPrimeTupleCoefficient (fun p => idealThetaCoeff η p * χ p) j n z / j.factorial := by
  have h := squarefree_roughPrimeTupleCoefficient (twistedThetaArithmeticFunction η χ)
    (twistedThetaArithmeticFunction_isMultiplicative η χ) hn hrough hj
  change roughPrimeTupleCoefficient (fun p => idealThetaCoeff η p * χ p) j n z =
    (j.factorial : ℂ) * (idealThetaCoeff η n * χ n) at h
  rw [h]
  have hfac : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  field_simp

end ArtinMatthews
