module

public import ArtinMatthews.MarkedMemoryPathEndpointCapacity
public import ArtinMatthews.MarkedMemoryPathPrimeCount
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

/-! The actual pending cutoff follows from the proved active/orphan
count. The supplied source capacity is retained without enlargement. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)
  (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
  (hc : MarkedMemoryPathChoicesCompatible d hZ c)

theorem markedMemoryPathEndpoint_pending_le_active_add_orphans (t : ℕ) :
    (∑ j,((markedMemoryEndpointCanonicalData (markedMemoryPathEndpointData hZ d c hc)).pendingAt t j).card)≤
      Fintype.card J*((n+1)*(pads+1))+markedMemoryPathOrphanCount d c :=
  (markedMemoryPathEndpoint_pending_le_used hZ d c hc t).trans (markedMemoryPathUsedPrime_total_card_le d c)

theorem markedMemoryPathCapacity_of_orphan_count
    (hcap : Fintype.card J*((n+1)*(pads+1))+markedMemoryPathOrphanCount d c≤B) :
    MarkedMemoryPathCapacity hZ d c hc B :=
  markedMemoryPathCapacity_of_used_card hZ d c hc ((markedMemoryPathUsedPrime_total_card_le d c).trans hcap)

def markedMemoryPathEndpointFamily_of_orphan_count
    (hcap : Fintype.card J*((n+1)*(pads+1))+markedMemoryPathOrphanCount d c≤B) :
    MarkedMemoryEndpointFamily (A := MarkedMemoryPathUsedPrime d c) (n := n) hZ
      (markedMemoryActivePathSource (B := B) d) :=
  markedMemoryPathEndpointFamily_of_cutoff hZ d c hc (markedMemoryPathCapacity_of_orphan_count hZ d c hc hcap)

end
end ArtinMatthews
