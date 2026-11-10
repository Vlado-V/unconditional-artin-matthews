module

public import ArtinMatthews.MarkedMemoryIndependentRecoveredCapacity
public import ArtinMatthews.MarkedMemoryCappedPathIndex
public import ArtinMatthews.MarkedMemoryIndependentPathSource
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

/-! Reverse extraction lands in the genuinely finite capped path index.
The pending cap is derived from the original local laws, not added as
an inverse-coverage hypothesis. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (hinj : Function.Injective (markedMemoryIndependentPrime hZ d))
  (hempty : ∀ j,(d.lifespan j).initial=[])
  (hterminal : ∀ j,markedMemoryIndependentQueue hZ d (2*n+1) j=[])
  (hn : MarkedMemoryBirthNormalized hZ d)
  (order : Fin n → J → Equiv.Perm (Fin pads))
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ (markedMemoryIndependentHistory hZ d order))
  (s : MarkedRawState P (pads+1) B Z)
  (hs : markedMemoryIndependentState hZ d 0 (Nat.zero_le n)=s)

def markedMemoryIndependentCappedPathIndex : MarkedMemoryCappedPathIndex (n := n) hZ s where
  path := markedMemoryIndependentActivePath hZ d hinj
  choices := markedMemoryIndependentPathChoices hZ d
  compatible := markedMemoryIndependentPathChoices_compatible hZ d hinj order hempty hterminal hn ha
  capacity := markedMemoryIndependentRecoveredCapacity hZ d hinj hempty hterminal hn order ha
  source := (markedMemoryIndependentActivePath_source hZ d hinj hempty).trans hs

theorem markedMemoryIndependentCappedPathIndex_path :
    (markedMemoryIndependentCappedPathIndex hZ d hinj hempty hterminal hn order ha s hs).path=
      markedMemoryIndependentActivePath hZ d hinj := rfl

theorem markedMemoryIndependentCappedPathIndex_choices :
    (markedMemoryIndependentCappedPathIndex hZ d hinj hempty hterminal hn order ha s hs).choices=
      markedMemoryIndependentPathChoices hZ d := rfl

end
end ArtinMatthews
