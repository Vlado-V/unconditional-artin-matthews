module

public import ArtinMatthews.MarkedMemoryCopiedSlotQuotient
public import ArtinMatthews.MarkedPhysicalEndpointVectors
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

/-! The slot quotient for actual identity-labelled raw endpoints and the
literal physical boundary vector. Identity embeddings remain injective;
their prime labels may repeat. Actual edge choices are connected through
their exact target position, pending memory and incoming label. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section IdentityStates
variable {J : Type*} [Fintype J] {I : J → Type*}
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (label : (j : J) → I j → ↥(P j))

def markedMemoryIdentityRawState
    (ids : (j : J) → Fin (pads+1) ↪ I j) (z : Z) (m : MarkedRawMemory P B) :
    MarkedRawState P (pads+1) B Z := (z, (fun j k => label j (ids j k), m))

theorem markedMemoryIdentityRawState_slot_position
    (ids : (j : J) → Fin (pads+1) ↪ I j) (z : Z) (m : MarkedRawMemory P B)
    (σ : J → Equiv.Perm (Fin (pads+1))) :
    (markedRawSlotEquiv σ (markedMemoryIdentityRawState label ids z m)).1 = z := rfl

theorem markedMemoryIdentityRawState_slot_memory
    (ids : (j : J) → Fin (pads+1) ↪ I j) (z : Z) (m : MarkedRawMemory P B)
    (σ : J → Equiv.Perm (Fin (pads+1))) :
    (markedRawSlotEquiv σ (markedMemoryIdentityRawState label ids z m)).2.2 = m := rfl

variable (src dst : (j : J) → Fin (pads+1) ↪ I j) (out inc : J → Fin (pads+1))

theorem markedMemoryIdentityRawState_slot_copied
    (x y : Z) (m n : MarkedRawMemory P B) (pair : MarkedMemorySlotFamilyFiber src dst out inc) :
    ((markedRawActiveSplit pads)
      (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair)
        (markedMemoryIdentityRawState label src x m)).2.1).1 =
    ((markedRawActiveSplit pads)
      (markedRawSlotEquiv (markedMemorySlotFamilyTargetInverse src dst out inc pair)
        (markedMemoryIdentityRawState label dst y n)).2.1).1 := by
  funext j k
  change label j (src j ((pair j).1.1 k.castSucc)) =
    label j (dst j ((pair j).1.2.symm k.castSucc))
  exact congrArg (label j) ((pair j).2.2.2 k)

theorem markedMemoryIdentityRawState_slot_source_last
    (x : Z) (m : MarkedRawMemory P B) (pair : MarkedMemorySlotFamilyFiber src dst out inc) :
    ((markedRawActiveSplit pads)
      (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair)
        (markedMemoryIdentityRawState label src x m)).2.1).2 =
      fun j => label j (src j (out j)) := by
  funext j
  change label j (src j (markedMemorySlotFamilySource src dst out inc pair j (Fin.last pads))) = _
  rw [markedMemorySlotFamilySource_last]

theorem markedMemoryIdentityRawState_slot_target_last
    (y : Z) (n : MarkedRawMemory P B) (pair : MarkedMemorySlotFamilyFiber src dst out inc) :
    ((markedRawActiveSplit pads)
      (markedRawSlotEquiv (markedMemorySlotFamilyTargetInverse src dst out inc pair)
        (markedMemoryIdentityRawState label dst y n)).2.1).2 =
      fun j => label j (dst j (inc j)) := by
  funext j
  change label j (dst j (markedMemorySlotFamilyTargetInverse src dst out inc pair j (Fin.last pads))) = _
  rw [markedMemorySlotFamilyTargetInverse_last]

/-- The copied tuple is proved from identity matching. The three remaining
conditions are exactly the position, queue and incoming-label outputs of
the literal edge reconstruction. -/
theorem markedMemoryIdentity_slotChoice_target
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (x y : Z) (m n : MarkedRawMemory P B) (pair : MarkedMemorySlotFamilyFiber src dst out inc)
    (c : MarkedRawEdgeChoice hZ
      (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair)
        (markedMemoryIdentityRawState label src x m)))
    (hposition : c.target = y)
    (hmemory : markedRawEdgeTargetMemory hZ
      (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair)
        (markedMemoryIdentityRawState label src x m)) c = n)
    (hlast : markedRawEdgeTargetLast m c.promotions c.fresh = fun j => label j (dst j (inc j))) :
    markedRawEdgeTargetState hZ
      (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair)
        (markedMemoryIdentityRawState label src x m)) c =
      markedRawSlotEquiv (markedMemorySlotFamilyTargetInverse src dst out inc pair)
        (markedMemoryIdentityRawState label dst y n) := by
  apply Prod.ext hposition
  apply Prod.ext _ hmemory
  apply (markedRawActiveSplit pads).injective
  change (markedRawActiveSplit pads) ((markedRawActiveSplit pads).symm _) = _
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · exact markedMemoryIdentityRawState_slot_copied label src dst out inc x y m n pair
  · exact hlast.trans (markedMemoryIdentityRawState_slot_target_last label src dst out inc y n pair).symm
end IdentityStates

section PhysicalCoefficient
variable {J : Type*} [Fintype J] [DecidableEq J] {I : J → Type*}
  [∀ j, DecidableEq (I j)] {P : J → Finset ℕ} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
  (label : (j : J) → I j → ↥(markedRawPrimeBand (P j)))
  (src dst : (j : J) → Fin (pads+1) ↪ I j) (out inc : J → Fin (pads+1))
  (hremaining : ∀ j, (markedMemoryBirthBatch (src j)).erase (src j (out j)) =
    (markedMemoryBirthBatch (dst j)).erase (dst j (inc j)))

include hremaining

/-- This is the original physical endpoint vector, with its support and
coefficient factors, not an assumed symmetric replacement. -/
theorem markedMemoryPhysical_slotFiber_weighted_sum
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ) (α β : ℕ → ℂ)
    (x y : Z) (m n : MarkedRawMemory (fun j => markedRawPrimeBand (P j)) B) :
    (∑ pair : MarkedMemorySlotFamilyFiber src dst out inc,
      (Fintype.card (J → Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹ *
        markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ
          (fun u => markedPhysicalEndpointVector P (pads+1) α β u.1.1)
          (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair)
            (markedMemoryIdentityRawState label src x m))
          (markedRawSlotEquiv (markedMemorySlotFamilyTargetInverse src dst out inc pair)
            (markedMemoryIdentityRawState label dst y n)) *
        (Fintype.card (J → Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹) =
      ((pads.factorial : ℂ) ^ Fintype.card J /
        (((pads+1).factorial : ℂ) ^ Fintype.card J)^2) *
      markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ
        (fun u => markedPhysicalEndpointVector P (pads+1) α β u.1.1)
        (markedRawSlotEquiv (fun j => Equiv.swap (Fin.last pads) (out j))
          (markedMemoryIdentityRawState label src x m))
        (markedRawSlotEquiv (fun j => Equiv.swap (Fin.last pads) (inc j))
          (markedMemoryIdentityRawState label dst y n)) :=
  markedRawEdgeJointCoefficient_slotFiber_weighted_sum hZ src dst out inc hremaining
    ψ η d₀ Y Q ρ (fun z _ => markedPhysicalEndpointVector P (pads+1) α β z.1)
    (markedMemoryIdentityRawState label src x m) (markedMemoryIdentityRawState label dst y n)

/-- The same quotient for literal store/promote coefficients. Queue,
position and incoming-label conditions identify each actual target;
there is no coefficient-invariance premise. -/
theorem markedMemoryPhysical_slotChoice_weighted_sum
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ) (α β : ℕ → ℂ)
    (x y : Z) (m n : MarkedRawMemory (fun j => markedRawPrimeBand (P j)) B)
    (c : (pair : MarkedMemorySlotFamilyFiber src dst out inc) → MarkedRawEdgeChoice hZ
      (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair)
        (markedMemoryIdentityRawState label src x m)))
    (hposition : ∀ pair, (c pair).target = y)
    (hmemory : ∀ pair, markedRawEdgeTargetMemory hZ
      (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair)
        (markedMemoryIdentityRawState label src x m)) (c pair) = n)
    (hlast : ∀ pair, markedRawEdgeTargetLast m (c pair).promotions (c pair).fresh =
      fun j => label j (dst j (inc j))) :
    (∑ pair : MarkedMemorySlotFamilyFiber src dst out inc,
      (Fintype.card (J → Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹ *
        markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ
          (fun u => markedPhysicalEndpointVector P (pads+1) α β u.1.1)
          (markedRawSlotEquiv (markedMemorySlotFamilySource src dst out inc pair)
            (markedMemoryIdentityRawState label src x m)) (c pair) *
        (Fintype.card (J → Equiv.Perm (Fin (pads+1))) : ℂ)⁻¹) =
      ((pads.factorial : ℂ) ^ Fintype.card J /
        (((pads+1).factorial : ℂ) ^ Fintype.card J)^2) *
      markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ
        (fun u => markedPhysicalEndpointVector P (pads+1) α β u.1.1)
        (markedRawSlotEquiv (fun j => Equiv.swap (Fin.last pads) (out j))
          (markedMemoryIdentityRawState label src x m))
        (markedRawSlotEquiv (fun j => Equiv.swap (Fin.last pads) (inc j))
          (markedMemoryIdentityRawState label dst y n)) := by
  simp_rw [markedRawEdgeChoiceCoefficient_eq_joint hZ ψ η d₀ Y Q ρ,
    markedMemoryIdentity_slotChoice_target label src dst out inc hZ x y m n _ _
      (hposition _) (hmemory _) (hlast _)]
  exact markedMemoryPhysical_slotFiber_weighted_sum hZ label src dst out inc hremaining
    ψ η d₀ Y Q ρ α β x y m n
end PhysicalCoefficient

end
end ArtinMatthews
