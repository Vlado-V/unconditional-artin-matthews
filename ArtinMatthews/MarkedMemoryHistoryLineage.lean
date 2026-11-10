module

public import ArtinMatthews.MarkedMemoryHistoryGhostOrigins
public import ArtinMatthews.MarkedMemoryHistoryEdgeSlotOrigins
public import ArtinMatthews.MarkedMemoryHistoryOriginComposition
public import ArtinMatthews.MarkedMemoryHistoryBirths
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

/-! Genuine recursive lineage of the actual final indexed population.
Every surviving particle comes from one initial index or one actually
performed birth, without identifying equal numeric prime values. -/
namespace ArtinMatthews
noncomputable section

def markedMemoryHistoryTerminalOrigin {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) →
      MarkedMemoryPopulationIndex (markedMemoryChronologicalTarget hZ history) ↪
        (MarkedMemoryPopulationIndex s ⊕ MarkedMemoryHistoryBirths hZ history)
  | 0,s,ghost => markedMemoryGhostPopulationOrigin hZ s ghost
  | _+1,s,history =>
      markedMemoryOriginCompose
        (markedMemoryOriginCompose (markedMemoryHistoryTerminalOrigin hZ history.2.2)
          (markedMemoryEdgeSlotPopulationOrigin hZ
            (markedMemoryGhostChoiceTarget hZ s history.1) history.2.1))
        (markedMemoryGhostPopulationOrigin hZ s history.1)

/-- The actual terminal lineage preserves the literal prime label. -/
theorem markedMemoryHistoryTerminalOrigin_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {n : ℕ}
    {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (i : MarkedMemoryPopulationIndex (markedMemoryChronologicalTarget hZ history)) :
    Sum.elim (markedMemoryPopulationPrime s) (markedMemoryHistoryBirthPrime hZ history)
      (markedMemoryHistoryTerminalOrigin hZ history i) =
        markedMemoryPopulationPrime (markedMemoryChronologicalTarget hZ history) i := by
  induction n generalizing s with
  | zero => exact markedMemoryGhostPopulationOrigin_prime hZ s history i
  | succ n ih =>
    exact markedMemoryOriginCompose_mark _ _ _ _ _ _ _
      (markedMemoryOriginCompose_mark _ _ _ _ _ _ _
        (ih history.2.2) (markedMemoryEdgeSlotPopulationOrigin_prime hZ _ history.2.1))
      (markedMemoryGhostPopulationOrigin_prime hZ s history.1) i

/-- Distinct final indexed particles always have distinct origin identities,
independently of the separate global distinctness condition on numeric marks. -/
theorem markedMemoryHistoryTerminalOrigin_injective {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    Function.Injective (markedMemoryHistoryTerminalOrigin hZ history) :=
  (markedMemoryHistoryTerminalOrigin hZ history).injective

end
end ArtinMatthews
