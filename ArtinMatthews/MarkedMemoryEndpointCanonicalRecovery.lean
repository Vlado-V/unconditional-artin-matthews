module

public import ArtinMatthews.MarkedMemoryEndpointLaws
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

/-! Canonical birth enumeration recovers the local laws of an arbitrary
finite tableau with empty initial pending memory. Equality of bare data
transports the actual finite birth-order fiber explicitly. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)

theorem markedMemoryEndpointOfData_canonical_laws
    (f : MarkedMemoryFiniteTableau (A := A) (P := P) (pads := pads) (B := B) hZ n)
    (hempty : ∀ j,markedMemoryFiniteList_toList (f.1.initial j)=[]) :
    MarkedMemoryFiniteTableauLaws hZ B (markedMemoryEndpointCanonicalData (markedMemoryEndpointOfData f.1)) := by
  have hd := markedMemoryEndpointOriginal_rebuild hZ f hempty
  have hl : MarkedMemoryFiniteTableauLaws hZ B
      (markedMemoryEndpointDataDecorated (markedMemoryEndpointOfData f.1)
        (markedMemoryEndpointOriginalBirths hZ f)) :=
    Eq.mpr (congrArg (MarkedMemoryFiniteTableauLaws hZ B) hd) f.2
  exact markedMemoryEndpointLaws_transfer hZ (markedMemoryEndpointOfData f.1)
    (markedMemoryEndpointOriginalBirths hZ f)
    (markedMemoryEndpointCanonicalBirths (markedMemoryEndpointOfData f.1)) hl

variable {d e : MarkedMemoryEndpointData A P pads Z n}

def markedMemoryEndpointTransportBirths (he : d=e) (births : MarkedMemoryEndpointBirthOrders e) :
    MarkedMemoryEndpointBirthOrders d := he.symm ▸ births

theorem markedMemoryEndpointDecorated_transport (he : d=e) (births : MarkedMemoryEndpointBirthOrders e) :
    markedMemoryEndpointDataDecorated d (markedMemoryEndpointTransportBirths he births)=
      markedMemoryEndpointDataDecorated e births := by
  cases he
  rfl

end
end ArtinMatthews
