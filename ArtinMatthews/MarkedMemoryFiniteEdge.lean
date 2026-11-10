module

public import ArtinMatthews.MarkedMemoryFiniteTableauRestriction
public import ArtinMatthews.MarkedMemoryIndependentEdge
public import ArtinMatthews.MarkedMemoryChoiceExt
public import ArtinMatthews.MarkedMemoryFiniteSlots
public import ArtinMatthews.MarkedMemoryFiniteTableauRecovery
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

/-! Every literal edge coordinate survives finite time restriction:
source/target slots, old promotion index, fresh label and store bit. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)} {n : ℕ}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

local notation "restored" => markedMemoryFiniteTableau_toIndependent hZ (markedMemoryIndependent_toFinite hZ d)

theorem markedMemoryFinite_restore_rawEdge_heq (v : ℕ) (hv : v<n)
    (order : J → Equiv.Perm (Fin pads)) :
    HEq (markedMemoryIndependentRawEdge hZ restored v hv order)
      (markedMemoryIndependentRawEdge hZ d v hv order) := by
  have hp := markedMemoryFinite_restore_position hZ d v (Nat.le_of_lt hv)
  have ht := markedMemoryFinite_restore_position hZ d (v+1) (by omega)
  have ha := markedMemoryFinite_restore_slottedActive hZ d v hv order
  have hq : markedMemoryIndependentQueue hZ restored (2*v+1)=markedMemoryIndependentQueue hZ d (2*v+1) :=
    funext (markedMemoryFinite_restore_queue hZ d (2*v+1) (by omega))
  have hi : (fun j => ((restored).lifespan j).incoming (2*v+1))=(fun j => (d.lifespan j).incoming (2*v+1)) :=
    funext (markedMemoryFinite_restore_incoming hZ d v hv)
  have ho : (fun j => ((restored).lifespan j).outgoing (2*v+1))=(fun j => (d.lifespan j).outgoing (2*v+1)) :=
    funext (markedMemoryFinite_restore_outgoing hZ d v hv)
  have hs : (fun j => decide (2*v+1 < ((restored).lifespan j).last (((restored).lifespan j).outgoing (2*v+1))))=
      (fun j => decide (2*v+1 < (d.lifespan j).last ((d.lifespan j).outgoing (2*v+1)))) := by
    funext j
    rw [markedMemoryFinite_restore_last,markedMemoryFinite_restore_outgoing hZ d v hv j]
  have hpart : (restored).particle=d.particle := rfl
  unfold markedMemoryIndependentRawEdge
  congr 1 <;> first | assumption | rfl | exact proof_irrel_heq _ _

theorem markedMemoryFinite_restore_edge_heq (v : ℕ) (hv : v<n)
    (order : J → Equiv.Perm (Fin pads)) :
    HEq (markedMemoryIndependentEdge hZ restored v hv order)
      (markedMemoryIndependentEdge hZ d v hv order) :=
  markedMemoryEdgeChoice_heq_of_fields hZ
    (markedMemoryFinite_restore_postGhost hZ d v (Nat.le_of_lt hv)) _ _
    (markedMemoryFinite_restore_sourceSlots hZ d v hv order)
    (markedMemoryFinite_restore_rawEdge_heq hZ d v hv order)
    (markedMemoryFinite_restore_targetSlots hZ d v hv order)

end
end ArtinMatthews
