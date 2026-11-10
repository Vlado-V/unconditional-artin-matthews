module

public import ArtinMatthews.MarkedMemoryPathEndpointData
public import ArtinMatthews.MarkedMemoryPrimeLifespanRecover
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

/-! Recovering optional ghost choices directly from the constructed
finite endpoint coordinates is an exact round trip. No chosen history
or inverse/correspondence premise is part of this decoding. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} {P : J → Finset Nat.Primes} {pads n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)
  (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
  (hc : MarkedMemoryPathChoicesCompatible d hZ c)

def markedMemoryPathEndpointDecodedChoices : MarkedMemoryPathPrimeChoices (P := P) (n := n) :=
  fun j p => if hu : MarkedMemoryPrimeLifespanUsed (markedMemoryPathVisits d j p) (c j p) then
    markedMemoryPrimeChoiceOfInterval
      ((markedMemoryPathEndpointData hZ d c hc).first j ⟨p,hu⟩)
      ((markedMemoryPathEndpointData hZ d c hc).last j ⟨p,hu⟩)
  else (none,none)

theorem markedMemoryPathEndpointDecodedChoices_eq :
    markedMemoryPathEndpointDecodedChoices hZ d c hc=c := by
  funext j p
  by_cases hu : MarkedMemoryPrimeLifespanUsed (markedMemoryPathVisits d j p) (c j p)
  · simp only [markedMemoryPathEndpointDecodedChoices,dite_eq_left hu]
    exact markedMemoryPrimeChoice_recover (markedMemoryPathPrimeLines hZ d p)
      (markedMemoryPathVisits d j p) (c j p) (hc j p) hu
  · simp only [markedMemoryPathEndpointDecodedChoices,dite_eq_right hu]
    exact (not_not.mp (fun hn => hu (Or.inr hn))).symm

end
end ArtinMatthews
