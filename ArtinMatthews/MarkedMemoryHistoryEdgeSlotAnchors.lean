module

public import ArtinMatthews.MarkedMemoryHistoryEdgeAnchors
public import ArtinMatthews.MarkedMemoryHistoryEdgeSlotOrigins
public import ArtinMatthews.MarkedMemoryHistoryEdgeOriginsPrime
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

/-! The exact prime-and-anchor transport for the actual global edge and
both literal endpoint slot symmetrizations. -/
namespace ArtinMatthews
noncomputable section

 theorem markedMemoryEdgePopulationOrigin_anchor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (hg : MarkedMemoryRawEdgeAnchorGate hZ s choice)
    (i : MarkedMemoryPopulationIndex (markedRawEdgeTargetState hZ s choice)) :
    Sum.elim (markedMemoryPopulationAnchor hZ s) (markedMemoryEdgeFreshOriginAnchor hZ s choice)
      (markedMemoryEdgePopulationOrigin hZ s choice i) =
        markedMemoryPopulationAnchor hZ (markedRawEdgeTargetState hZ s choice) i := by
  rcases i with ⟨j, i⟩ | ⟨j, i⟩
  · rw [markedMemoryEdgePopulationOrigin_active]
    have h := markedMemoryEdgeGroupOrigin_anchor hZ s choice hg j (Sum.inl i)
    generalize hout : markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inl i) = o at h ⊢
    rcases o with (old | old) | fresh
    all_goals exact h
  · erw [markedMemoryEdgePopulationOrigin_pending hZ s choice j i]
    have h := markedMemoryEdgeGroupOrigin_anchor hZ s choice hg j (Sum.inr i)
    generalize hout : markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inr i) = o at h ⊢
    rcases o with (old | old) | fresh
    all_goals exact h

 def MarkedMemoryEdgeAnchorGate {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedMemoryEdgeChoice hZ s) : Prop :=
  MarkedMemoryRawEdgeAnchorGate hZ (markedRawSlotEquiv choice.1 s) choice.2.1

 def markedMemoryEdgeBirthAnchor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P (pads+1) B Z}
    (choice : MarkedMemoryEdgeChoice hZ s) : MarkedMemoryEdgeBirthIndex choice → MarkedMemoryAnchoredPrime :=
  markedMemoryEdgeFreshOriginAnchor hZ (markedRawSlotEquiv choice.1 s) choice.2.1

 theorem markedMemoryEdgeSlotPopulationOrigin_anchor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedMemoryEdgeChoice hZ s) (hg : MarkedMemoryEdgeAnchorGate hZ s choice)
    (i : MarkedMemoryPopulationIndex (markedMemoryEdgeChoiceTarget hZ s choice)) :
    Sum.elim (markedMemoryPopulationAnchor hZ s) (markedMemoryEdgeBirthAnchor choice)
      (markedMemoryEdgeSlotPopulationOrigin hZ s choice i) =
        markedMemoryPopulationAnchor hZ (markedMemoryEdgeChoiceTarget hZ s choice) i := by
  let i₀ := markedMemorySlotPopulationEquiv choice.2.2
    (markedRawEdgeTargetState hZ (markedRawSlotEquiv choice.1 s) choice.2.1) i
  have h := markedMemoryEdgePopulationOrigin_anchor hZ (markedRawSlotEquiv choice.1 s) choice.2.1 hg i₀
  have ht := markedMemorySlotPopulationEquiv_anchor hZ choice.2.2
    (markedRawEdgeTargetState hZ (markedRawSlotEquiv choice.1 s) choice.2.1) i
  change Sum.elim (markedMemoryPopulationAnchor hZ s) (markedMemoryEdgeBirthAnchor choice)
      (Sum.map (markedMemorySlotPopulationEquiv choice.1 s) id
        (markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv choice.1 s) choice.2.1 i₀)) = _
  generalize ho : markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv choice.1 s) choice.2.1 i₀ = o at h ⊢
  cases o with
  | inl old =>
    simp only [Sum.map_inl, Sum.elim_inl] at h ⊢
    exact (markedMemorySlotPopulationEquiv_anchor hZ choice.1 s old).trans (h.trans ht)
  | inr birth =>
    simp only [Sum.map_inr, Sum.elim_inr, id_eq]
    exact h.trans ht

end
end ArtinMatthews
