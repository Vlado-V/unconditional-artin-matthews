module

public import ArtinMatthews.MarkedMemoryEndpointLaws
public import ArtinMatthews.MarkedMemoryPathEndpointData
public import ArtinMatthews.MarkedMemoryPathEndpointFields
public import ArtinMatthews.MarkedMemoryPrimeLifespanTerminal
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

/-! The derived bare endpoint family has no pending identity after
its final ghost. This is a literal finite-set statement, valid before
choosing any order for a birth batch. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)
  (c : (j : J) → ↥(P j) → MarkedMemoryPrimeLifespanChoice n)
  (hc : MarkedMemoryPathChoicesCompatible d hZ c)

local notation "C" => markedMemoryEndpointCanonicalData (markedMemoryPathEndpointData hZ d c hc)

theorem markedMemoryPathEndpoint_terminal_pending (j : J) : (C).pendingAt (2*n+1) j=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hm := (Finset.mem_filter.mp ha).2
  have hl : markedMemoryPrimeLast (markedMemoryPathVisits d j a.1) (c j a.1)=2*n+1 := by
    have hb := markedMemoryPrimeLast_bound (markedMemoryPathVisits d j a.1) (c j a.1)
    have hle := hm.2.1
    change 2*n+1≤ markedMemoryPrimeLast (markedMemoryPathVisits d j a.1) (c j a.1) at hle
    omega
  have hv := markedMemoryPrimeLast_terminal_active (markedMemoryPathVisits d j a.1) (c j a.1) hl
  have hh := (markedMemoryPathEndpoint_active_odd hZ d c hc (Fin.last n) j a).mpr
    ((markedMemoryPathVisits_mem d j a.1 (Fin.last n)).mp hv)
  exact hm.2.2 hh

end
end ArtinMatthews
