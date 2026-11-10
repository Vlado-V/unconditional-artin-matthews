module

public import ArtinMatthews.MarkedMemoryPathEndpointCapacity
public import ArtinMatthews.MarkedMemoryActivePathFinite
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

/-! A genuinely finite path-choice summation index at a fixed raw
boundary source. Only actual path fields, compatible optional endpoints
and the computed original pending capacity are stored. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)

structure MarkedMemoryCappedPathIndex where
  path : MarkedMemoryActivePathData P pads Z n
  choices : MarkedMemoryPathPrimeChoices (P := P) (n := n)
  compatible : MarkedMemoryPathChoicesCompatible path hZ choices
  capacity : MarkedMemoryPathCapacity hZ path choices compatible B
  source : markedMemoryActivePathSource (B := B) path=s

theorem markedMemoryCappedPathIndex_ext
    {a b : MarkedMemoryCappedPathIndex (n := n) hZ s}
    (hp : a.path=b.path) (hc : a.choices=b.choices) : a=b := by
  cases a
  cases b
  cases hp
  cases hc
  rfl

instance markedMemoryCappedPathIndex_finite : Finite (MarkedMemoryCappedPathIndex (n := n) hZ s) := by
  let encode := fun d : MarkedMemoryCappedPathIndex (n := n) hZ s => (d.path,d.choices)
  have hi : Function.Injective encode := by
    intro a b he
    exact markedMemoryCappedPathIndex_ext hZ s (congrArg Prod.fst he) (congrArg Prod.snd he)
  exact Finite.of_injective encode hi

instance markedMemoryCappedPathIndex_fintype : Fintype (MarkedMemoryCappedPathIndex (n := n) hZ s) :=
  Fintype.ofFinite _

abbrev MarkedMemoryCappedPathDecoratedIndex :=
  Σ i : MarkedMemoryCappedPathIndex (n := n) hZ s,
    MarkedMemoryEndpointBirthOrders (markedMemoryPathEndpointData hZ i.path i.choices i.compatible) ×
      (Fin n → J → Equiv.Perm (Fin pads))

instance markedMemoryCappedPathDecoratedIndex_fintype :
    Fintype (MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s) := by infer_instance

end
end ArtinMatthews
