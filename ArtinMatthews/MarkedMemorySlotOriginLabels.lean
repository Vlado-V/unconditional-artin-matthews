module

public import ArtinMatthews.MarkedMemoryEdgeOriginLabels
public import ArtinMatthews.MarkedMemoryHistoryEdgeSlotOrigins
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

/-! Identity-label compatibility with both actual endpoint slot
permutations. The raw edge rule is transported through the two genuine
population equivalences, with no symmetry assumption on labels. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {A : J → Type*} {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
  (choice : MarkedMemoryEdgeChoice hZ s)
  (activeId : (j : J) → Fin (pads+1) → A j)
  (pendingId : (j : J) → Fin (s.2.2.1.1 j : ℕ) → A j) (incoming : (j : J) → A j)

theorem markedMemoryEdgeSlotPopulationOrigin_label
    (hprom : ∀ j k, choice.2.1.promotions j = some k → pendingId j k = incoming j)
    (i : MarkedMemoryPopulationIndex (markedMemoryEdgeChoiceTarget hZ s choice)) :
    Sum.elim (markedMemoryEdgeSourceLabel s activeId pendingId)
      (markedMemoryEdgeFreshLabel hZ (markedRawSlotEquiv choice.1 s) choice.2.1 incoming)
      (markedMemoryEdgeSlotPopulationOrigin hZ s choice i) =
        markedMemoryEdgeTargetLabel hZ (markedRawSlotEquiv choice.1 s) choice.2.1
          (fun j k => activeId j (choice.1 j k)) pendingId incoming
          (markedMemorySlotPopulationEquiv choice.2.2
            (markedRawEdgeTargetState hZ (markedRawSlotEquiv choice.1 s) choice.2.1) i) := by
  let i₀ := markedMemorySlotPopulationEquiv choice.2.2
    (markedRawEdgeTargetState hZ (markedRawSlotEquiv choice.1 s) choice.2.1) i
  have h := markedMemoryEdgePopulationOrigin_label hZ (markedRawSlotEquiv choice.1 s) choice.2.1
    (fun j k => activeId j (choice.1 j k)) pendingId incoming hprom i₀
  change Sum.elim (markedMemoryEdgeSourceLabel s activeId pendingId)
    (markedMemoryEdgeFreshLabel hZ (markedRawSlotEquiv choice.1 s) choice.2.1 incoming)
    (Sum.map (markedMemorySlotPopulationEquiv choice.1 s) id
      (markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv choice.1 s) choice.2.1 i₀)) = _
  generalize ho : markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv choice.1 s) choice.2.1 i₀ = o at h ⊢
  cases o with
  | inl old =>
    exact (markedMemoryEdgeSourceLabel_slots s activeId pendingId choice.1 old).trans h
  | inr birth => exact h

end
end ArtinMatthews
