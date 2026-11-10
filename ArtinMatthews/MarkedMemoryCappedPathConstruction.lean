module

public import ArtinMatthews.MarkedMemoryPathEndpointCapacity
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

/-! The independent tableau of a compatible prime path at its actual
pending capacity. Birth orders are retained explicitly; all interval,
active and particle fields come from the computed bare family. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)
  (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
  (hc : MarkedMemoryPathChoicesCompatible d hZ c)
  (hcap : MarkedMemoryPathCapacity hZ d c hc B)

local notation "E" => markedMemoryPathEndpointData hZ d c hc

def markedMemoryCappedPathTableau (births : MarkedMemoryEndpointBirthOrders E) :
    @MarkedMemoryFiniteTableau J inferInstance (MarkedMemoryPathUsedPrime d c)
      (markedMemoryPathUsedPrime_fintype d c) P pads B Z hZ n :=
    ⟨markedMemoryEndpointDataDecorated E births,
      markedMemoryEndpointLaws_transfer hZ E (markedMemoryEndpointCanonicalBirths E) births
        (markedMemoryPathEndpoint_laws_of_cutoff hZ d c hc hcap)⟩

theorem markedMemoryCappedPathTableau_data (births : MarkedMemoryEndpointBirthOrders E) :
    (markedMemoryCappedPathTableau (B := B) hZ d c hc hcap births).1=
      markedMemoryEndpointDataDecorated E births := rfl

def markedMemoryCappedPathIndependent (births : MarkedMemoryEndpointBirthOrders E) :
    @MarkedMemoryIndependentLifespans J inferInstance (MarkedMemoryPathUsedPrime d c)
      (markedMemoryPathUsedPrime_fintype d c) P pads B Z hZ n :=
  markedMemoryFiniteTableau_toIndependent hZ (markedMemoryCappedPathTableau (B := B) hZ d c hc hcap births)

end
end ArtinMatthews
