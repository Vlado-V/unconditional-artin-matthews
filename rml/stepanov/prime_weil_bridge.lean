module

public import rml.weil.prime_foundation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
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
public import rml.stepanov.prime_weil

@[expose] public section

/-!
# Prime-bound normalization

Transfers the proved prime estimate to the coefficient convention of Harcos (2015),
equation (1), and Weil’s classical statement.
-/

namespace RML.ExpSum.Stepanov

open RML.ExpSum.Weil

/-- Prime nondegenerate Weil bound proved using the Stepanov–Carlitz route. -/
theorem primeNondegenerateWeil_proved :
    PrimeNondegenerateWeil :=
  (primeNondegenerateWeil_iff_oneParameter).2
    oneParameterPrimeWeil_proved

/-- The classical Weil statement follows from the normalization equivalence. -/
theorem weil1948PrimeKloostermanBound_proved :
    Weil1948PrimeKloostermanBound :=
  (primeNondegenerateWeil_iff_weil1948).1
    primeNondegenerateWeil_proved

#print axioms primeNondegenerateWeil_proved
#print axioms weil1948PrimeKloostermanBound_proved

end RML.ExpSum.Stepanov
