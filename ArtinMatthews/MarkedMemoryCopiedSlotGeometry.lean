module

public import ArtinMatthews.MarkedMinorArcRawEdgeJointCoefficient
public import ArtinMatthews.MarkedMinorArcRawSlotAverage
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeOmissionAverage
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeSlotGeometry
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual copied-slot geometry of the coupled raw edge. All endpoint
distinctness, pending damping, determinant, cutoff and cross-ban factors
are retained. An arbitrary ordered-state multiplier is factored out
explicitly rather than assumed invariant. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

omit [DecidableEq J] in
theorem markedRawEndpointFactor_test_factor (ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    markedRawEndpointFactor hZ ρ χ s = markedRawEndpointFactor hZ ρ (fun _ => 1) s * χ s := by
  unfold markedRawEndpointFactor
  split_ifs <;> simp only [mul_one, zero_mul]

omit [DecidableEq J] in
theorem markedRawEndpointFactor_slots_positionMemory (ρ : ℝ)
    (F : Z → MarkedRawMemory P B → ℂ)
    (σ : J → Equiv.Perm (Fin (pads+1))) (s : MarkedRawState P (pads+1) B Z) :
    markedRawEndpointFactor hZ ρ (fun u => F u.1 u.2.2) (markedRawSlotEquiv σ s) =
      markedRawEndpointFactor hZ ρ (fun u => F u.1 u.2.2) s := by
  have hd := markedDirtyRawStateSlot_distinct_iff σ s
  change MarkedRawActiveDistinct (markedRawSlotEquiv σ s).2.1 ↔ MarkedRawActiveDistinct s.2.1 at hd
  unfold markedRawEndpointFactor
  change (if MarkedRawActiveDistinct (markedRawSlotEquiv σ s).2.1 then
      ((ρ ^ markedRawPendingHits s.2.2 s.1.1 (hZ _ s.1.2) : ℝ) : ℂ) * F s.1 s.2.2 else 0) = _
  rw [propext hd]

theorem markedRawCopiedProduct_slots_same_out
    (σ τ : J → Equiv.Perm (Fin (pads+1))) (s : MarkedRawState P (pads+1) B Z)
    (hlast : ∀ j, σ j (Fin.last pads) = τ j (Fin.last pads)) :
    markedRawCopiedProduct ((markedRawActiveSplit pads) (markedRawSlotEquiv σ s).2.1).1 =
      markedRawCopiedProduct ((markedRawActiveSplit pads) (markedRawSlotEquiv τ s).2.1).1 := by
  rw [markedDirtyRawStateSlot_copied_product, markedDirtyRawStateSlot_copied_product]
  exact congrArg (markedSourceCopiedProduct (markedRawNumericActive s.2.1)) (funext hlast)

omit [DecidableEq J] in
theorem markedRawLastSlots_same_out
    (σ τ : J → Equiv.Perm (Fin (pads+1))) (s : MarkedRawState P (pads+1) B Z)
    (hlast : ∀ j, σ j (Fin.last pads) = τ j (Fin.last pads)) :
    ((markedRawActiveSplit pads) (markedRawSlotEquiv σ s).2.1).2 =
      ((markedRawActiveSplit pads) (markedRawSlotEquiv τ s).2.1).2 := by
  funext j
  exact congrArg (s.2.1 j) (hlast j)

/-- The physical coupled coefficient is independent of both internal
slot orders once the two omitted slots have been fixed. -/
theorem markedRawEdgeJointCoefficient_slots_core
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (s t : MarkedRawState P (pads+1) B Z)
    (σ σ' τ τ' : J → Equiv.Perm (Fin (pads+1)))
    (hs : ∀ j, σ j (Fin.last pads) = σ' j (Fin.last pads))
    (ht : ∀ j, τ j (Fin.last pads) = τ' j (Fin.last pads)) :
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ (fun _ => 1)
      (markedRawSlotEquiv σ s) (markedRawSlotEquiv τ t) =
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ (fun _ => 1)
      (markedRawSlotEquiv σ' s) (markedRawSlotEquiv τ' t) := by
  have hd := markedRawCopiedProduct_slots_same_out σ σ' s hs
  have hsl := markedRawLastSlots_same_out σ σ' s hs
  have htl := markedRawLastSlots_same_out τ τ' t ht
  have hb : MarkedRawFullCrossBan (markedRawSlotEquiv σ s).2.1
      ((markedRawActiveSplit pads) (markedRawSlotEquiv τ t).2.1).2 ↔
      MarkedRawFullCrossBan (markedRawSlotEquiv σ' s).2.1
      ((markedRawActiveSplit pads) (markedRawSlotEquiv τ' t).2.1).2 := by
    rw [htl]
    exact (markedDirtyRawStateSlot_crossBan_iff σ s _).trans
      (markedDirtyRawStateSlot_crossBan_iff σ' s _).symm
  have heσ := markedRawEndpointFactor_slots_positionMemory hZ ρ (fun _ _ => 1) σ s
  have heσ' := markedRawEndpointFactor_slots_positionMemory hZ ρ (fun _ _ => 1) σ' s
  have heτ := markedRawEndpointFactor_slots_positionMemory hZ ρ (fun _ _ => 1) τ t
  have heτ' := markedRawEndpointFactor_slots_positionMemory hZ ρ (fun _ _ => 1) τ' t
  unfold markedRawEdgeJointCoefficient
  dsimp only
  rw [propext hb, hd, hsl, htl, heσ, heσ', heτ, heτ']
  rfl

/-- Every original ordered label/memory observable remains visible.
Only the physical coupled coefficient is extracted from it. -/
theorem markedRawEdgeJointCoefficient_test_factor
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s t : MarkedRawState P (pads+1) B Z) :
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ s t =
      markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ (fun _ => 1) s t * χ s * χ t := by
  unfold markedRawEdgeJointCoefficient
  dsimp only
  split_ifs <;> try simp only [zero_mul]
  rw [markedRawEndpointFactor_test_factor hZ ρ χ s, markedRawEndpointFactor_test_factor hZ ρ χ t]
  ring

theorem markedRawEdgeJointCoefficient_slots_positionMemory
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (F : Z → MarkedRawMemory P B → ℂ) (s t : MarkedRawState P (pads+1) B Z)
    (σ σ' τ τ' : J → Equiv.Perm (Fin (pads+1)))
    (hs : ∀ j, σ j (Fin.last pads) = σ' j (Fin.last pads))
    (ht : ∀ j, τ j (Fin.last pads) = τ' j (Fin.last pads)) :
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ (fun u => F u.1 u.2.2)
      (markedRawSlotEquiv σ s) (markedRawSlotEquiv τ t) =
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ (fun u => F u.1 u.2.2)
      (markedRawSlotEquiv σ' s) (markedRawSlotEquiv τ' t) := by
  rw [markedRawEdgeJointCoefficient_test_factor hZ ψ η d₀ Y Q ρ (fun u => F u.1 u.2.2)
      (markedRawSlotEquiv σ s) (markedRawSlotEquiv τ t),
    markedRawEdgeJointCoefficient_test_factor hZ ψ η d₀ Y Q ρ (fun u => F u.1 u.2.2)
      (markedRawSlotEquiv σ' s) (markedRawSlotEquiv τ' t),
    markedRawEdgeJointCoefficient_slots_core hZ ψ η d₀ Y Q ρ s t σ σ' τ τ' hs ht]
  rfl

end
end ArtinMatthews
