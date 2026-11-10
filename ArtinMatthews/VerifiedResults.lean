module

public import ArtinMatthews.RealDensity
public import ArtinMatthews.ObstructionA
public import ArtinMatthews.ObstructionB
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





/-!
# Verified components of the Artin–Matthews formalization

This module proves the finite-obstruction direction and states
`FullMainStatement`. The proof of the full statement is in
`ArtinMatthews.FullMainActual`.
-/

namespace ArtinMatthews

/-- The finite-obstruction branch of Theorem 1.1, with an explicit exceptional set. -/
theorem obstruction_prime_eq_two {S : Finset ℤ} (h : ObstructionA S ∨ ObstructionB S)
    {p : ℕ} (hp : p ∈ SimultaneousPrimitivePrimes S) : p = 2 := by
  rcases h with hA | hB
  · exact obstructionA_prime_eq_two hA hp
  · exact obstructionB_prime_eq_two hB hp

/-- Either Matthews obstruction implies finiteness, without any analytic hypothesis. -/
theorem finite_of_obstruction {S : Finset ℤ} (h : ObstructionA S ∨ ObstructionB S) :
    (SimultaneousPrimitivePrimes S).Finite := by
  rcases h with hA | hB
  · exact obstructionA_finite hA
  · exact obstructionB_finite hB

/-- The real-cutoff relative lower density is zero in the obstruction cases. -/
theorem zero_relative_lower_density_of_obstruction {S : Finset ℤ}
    (h : ObstructionA S ∨ ObstructionB S) :
    Filter.liminf (realRelativePrimeDensity S) Filter.atTop = 0 :=
  realRelativePrimeDensity_liminf_zero_of_finite (finite_of_obstruction h)

/-- Full target, including the exact real-cutoff density consequence.
This is a proposition definition, not a proof of the positive case. -/
def FullMainStatement : Prop :=
  ∀ S : Finset ℤ, AdmissibleBases S →
    ((¬ ObstructionA S ∧ ¬ ObstructionB S) →
      PositiveDyadicLowerBound S ∧ PositiveRealLowerRelativePrimeDensity S) ∧
    ((ObstructionA S ∨ ObstructionB S) → (SimultaneousPrimitivePrimes S).Finite)

end ArtinMatthews
