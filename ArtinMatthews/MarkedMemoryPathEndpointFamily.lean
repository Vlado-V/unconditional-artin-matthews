module

public import ArtinMatthews.MarkedMemoryPathEndpointLaws
public import ArtinMatthews.MarkedMemorySourceBoundary
public import ArtinMatthews.MarkedMemoryEndpointFamily
public import ArtinMatthews.MarkedMemoryInitialMeasure
public import ArtinMatthews.MarkedMemoryPathEndpointFields
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

/-! Forward construction of the honest bare endpoint family attached
to a fixed active path and compatible primewise choices. Its source is
the actual initial path marking with empty pending memory. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)
  (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
  (hc : MarkedMemoryPathChoicesCompatible d hZ c)

def markedMemoryActivePathSource : MarkedRawState P (pads+1) B Z :=
  markedMemoryBoundarySource (B := B) (d.position 0) (fun j k => d.active 0 j k)

local notation "Used" => MarkedMemoryPathUsedPrime d c
local notation "E" => markedMemoryPathEndpointData hZ d c hc
local notation "C" => markedMemoryEndpointCanonicalData E

def markedMemoryPathEndpointFamily (hB : (∑ j,(P j).card)≤B) :
    MarkedMemoryEndpointFamily (A := Used) (n := n) hZ (markedMemoryActivePathSource (B := B) d) := by
  let hl := markedMemoryPathEndpoint_laws hZ d c hc hB
  let f : MarkedMemoryFiniteTableau (A := Used) (P := P) (pads := pads) (B := B) hZ n := ⟨C,hl⟩
  let g := markedMemoryFiniteTableau_toIndependent hZ f
  refine ⟨E,⟨hl,?_,?_⟩⟩
  · have he : ∀ j,(g.lifespan j).initial=[] := by
      intro j
      change markedMemoryFiniteList_toList (markedMemoryFiniteList_ofList [] List.nodup_nil)=[]
      exact markedMemoryFiniteList_toList_ofList [] List.nodup_nil
    have hm := markedMemory_initial_memory_empty hZ g he
    change markedMemoryIndependentState hZ g 0 (Nat.zero_le n)=_
    unfold markedMemoryIndependentState
    rw [hm]
    apply Prod.ext
    · exact markedMemoryPathEndpoint_positionAt hZ d c hc 0
    · apply Prod.ext
      · rfl
      · rfl
  · apply (markedMemoryFiniteAnchorNormalize_fixed_iff hZ C).mpr
    exact markedMemoryPathEndpoint_anchor hZ d c hc

end
end ArtinMatthews
