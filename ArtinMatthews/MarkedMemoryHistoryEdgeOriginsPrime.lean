module

public import ArtinMatthews.MarkedMemoryHistoryEdgeOrigins
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Prime-label preservation for the genuine global edge-population origin injection. -/
namespace ArtinMatthews
noncomputable section

/-- The prime of an actually performed fresh edge birth. Promoted groups have no such address. -/
def markedMemoryEdgeFreshOriginPrime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) : {j : J // choice.promotions j = none} → Nat.Primes :=
  fun j => (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh j.1).1

/-- Plain indexed formula for an active target slot's global origin. -/
theorem markedMemoryEdgePopulationOrigin_active {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (j : J) (i : Fin (pads+1)) :
    markedMemoryEdgePopulationOrigin hZ s choice (Sum.inl ⟨j, i⟩) =
      Sum.map (Sum.map (Sigma.mk j) (Sigma.mk j))
        (fun h : PLift (choice.promotions j = none) => ⟨j, h.down⟩)
        (markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inl i)) := by
  change (Equiv.sumCongr (markedMemoryPopulationGroupEquiv s).symm
    (Equiv.sigmaPLiftEquivSubtype (fun j => choice.promotions j = none)))
      ((Equiv.sigmaSumDistrib
        (fun j => Fin (pads+1) ⊕ Fin (s.2.2.1.1 j : ℕ))
        (fun j => PLift (choice.promotions j = none)))
        ⟨j, markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inl i)⟩) = _
  generalize hout : markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inl i) = o
  rcases o with (old | old) | fresh <;> rfl

/-- Plain indexed formula for a pending target slot's global origin. -/
theorem markedMemoryEdgePopulationOrigin_pending {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (j : J)
    (i : Fin ((markedRawEdgeTargetMemory hZ s choice).1.1 j : ℕ)) :
    markedMemoryEdgePopulationOrigin hZ s choice (Sum.inr ⟨j, i⟩) =
      Sum.map (Sum.map (Sigma.mk j) (Sigma.mk j))
        (fun h : PLift (choice.promotions j = none) => ⟨j, h.down⟩)
        (markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inr i)) := by
  change (Equiv.sumCongr (markedMemoryPopulationGroupEquiv s).symm
    (Equiv.sigmaPLiftEquivSubtype (fun j => choice.promotions j = none)))
      ((Equiv.sigmaSumDistrib
        (fun j => Fin (pads+1) ⊕ Fin (s.2.2.1.1 j : ℕ))
        (fun j => PLift (choice.promotions j = none)))
        ⟨j, markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inr i)⟩) = _
  generalize hout : markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inr i) = o
  rcases o with (old | old) | fresh <;> rfl

/-- The actual global indexed route preserves every target prime, including repeated values. -/
theorem markedMemoryEdgePopulationOrigin_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s)
    (i : MarkedMemoryPopulationIndex (markedRawEdgeTargetState hZ s choice)) :
    Sum.elim (markedMemoryPopulationPrime s) (markedMemoryEdgeFreshOriginPrime hZ s choice)
      (markedMemoryEdgePopulationOrigin hZ s choice i) =
        markedMemoryPopulationPrime (markedRawEdgeTargetState hZ s choice) i := by
  rcases i with ⟨j, i⟩ | ⟨j, i⟩
  · rw [markedMemoryEdgePopulationOrigin_active]
    have h := markedMemoryEdgeGroupOrigin_prime hZ s choice j (Sum.inl i)
    change Sum.elim (markedMemoryPopulationGroupPrime s j)
      (fun _ : PLift (choice.promotions j = none) =>
        (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh j).1)
      (markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inl i)) = ((markedRawEdgeTargetState hZ s choice).2.1 j i).1 at h
    generalize hout : markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inl i) = o at h ⊢
    rcases o with (old | old) | fresh
    all_goals
      simpa only [Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr,
        markedMemoryPopulationPrime, markedMemoryPopulationGroupPrime,
        markedMemoryEdgeFreshOriginPrime] using h
  · erw [markedMemoryEdgePopulationOrigin_pending hZ s choice j i]
    have h := markedMemoryEdgeGroupOrigin_prime hZ s choice j (Sum.inr i)
    change Sum.elim (markedMemoryPopulationGroupPrime s j)
      (fun _ : PLift (choice.promotions j = none) =>
        (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh j).1)
      (markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inr i)) = ((markedRawEdgeTargetState hZ s choice).2.2.2 j i).1.1 at h
    generalize hout : markedMemoryEdgeGroupOrigin hZ s choice j (Sum.inr i) = o at h ⊢
    rcases o with (old | old) | fresh
    all_goals
      simpa only [Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr,
        markedMemoryPopulationPrime, markedMemoryPopulationGroupPrime,
        markedMemoryEdgeFreshOriginPrime] using h

end
end ArtinMatthews
