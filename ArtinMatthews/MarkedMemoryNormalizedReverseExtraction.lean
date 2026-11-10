module

public import ArtinMatthews.MarkedMemoryBandAddressEquiv
public import ArtinMatthews.MarkedMemoryActualSlotOrder
public import ArtinMatthews.MarkedMemoryHistorySlotSchedule
public import ArtinMatthews.MarkedMemoryNormalizedAnchors
public import ArtinMatthews.MarkedMemoryActualStateReconstruction
public import ArtinMatthews.MarkedMemoryBirthAnchor
public import ArtinMatthews.MarkedMemoryFiniteRecoveryExt
public import ArtinMatthews.MarkedMemoryFiniteRelabelNaturality
public import ArtinMatthews.MarkedMemoryIndependentOrderMultiplicity
public import ArtinMatthews.MarkedMemoryIndependentRelabelSlots
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

/-! Re-extracting an assembled normalized tableau recovers every finite
field up to its derived bandwise address equivalence, and recovers the
copied-slot orders exactly. No numeric distinctness or coverage premise
is used: identities remain actual indexed trace addresses. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

local notation "history" => markedMemoryIndependentHistory hZ d order
local notation "rename" => markedMemoryBandAddressEquiv hZ d order

theorem markedMemoryHistoryVertexEdge_sourceSlots
    {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) (v : Fin n) :
    (markedMemoryHistoryVertexEdge hZ H v).1=markedMemoryHistorySourceSlots hZ H v := by
  induction n generalizing s with
  | zero => exact Fin.elim0 v
  | succ n ih =>
    refine Fin.cases ?_ (fun w => ?_) v
    · rfl
    · exact ih H.2.2 w

theorem markedMemoryBandAddressEquiv_particle
    (hempty : ∀ j,((markedMemoryIndependentState hZ d 0 (Nat.zero_le n)).2.2.1.1 j:ℕ)=0)
    (hn : MarkedMemoryBirthNormalized hZ d)
    (j : J) (a : MarkedMemoryActualFiber hZ history j) :
    markedMemoryActualParticle hZ history j a=d.particle j (rename j a) := by
  have hv : (d.lifespan j).first (rename j a)/2≤n := by
    have hf := (d.lifespan j).nonempty (rename j a)
    have hl := (d.lifespan j).bounded (rename j a)
    omega
  rw [markedMemoryActualParticle_birthPosition hZ history hempty j a,
    markedMemoryBandAddressEquiv_prime hZ d order j a,
    markedMemoryBandAddressEquiv_first hZ d order j a,
    markedMemoryBandAddressEquiv_position hZ d order _ hv]
  exact (hn j (rename j a)).symm

theorem markedMemoryNormalized_reverse_extraction
    (hempty : ∀ j,((markedMemoryIndependentState hZ d 0 (Nat.zero_le n)).2.2.1.1 j:ℕ)=0)
    (hn : MarkedMemoryBirthNormalized hZ d)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) :
    markedMemoryIndependent_toFinite hZ
        (markedMemoryIndependentRelabel hZ rename (markedMemoryActualTableau hZ history ha))=
      markedMemoryIndependent_toFinite hZ d := by
  apply markedMemoryFinite_recovery_ext hZ
  · intro j a
    change markedMemoryActualFirst hZ history j ((rename j).symm a)=(d.lifespan j).first a
    simpa only [Equiv.apply_symm_apply] using markedMemoryBandAddressEquiv_first hZ d order j ((rename j).symm a)
  · intro j a
    change markedMemoryActualLast hZ history j ((rename j).symm a)=(d.lifespan j).last a
    simpa only [Equiv.apply_symm_apply] using markedMemoryBandAddressEquiv_last hZ d order j ((rename j).symm a)
  · intro t ht j a
    change markedMemoryActualActive hZ history t j ((rename j).symm a) ↔ (d.lifespan j).active t a
    simpa only [Equiv.apply_symm_apply] using markedMemoryBandAddressEquiv_active hZ d order t ht j ((rename j).symm a)
  · intro v hv
    exact markedMemoryBandAddressEquiv_position hZ d order v hv
  · intro v hv j
    apply Function.Embedding.ext
    intro k
    change rename j (markedMemoryActualActiveIds hZ history (2*v) j k)=d.activeId v j k
    simpa only [show 2*v/2=v by omega] using markedMemoryBandAddressEquiv_activeId hZ d order (2*v) (by omega) j k
  · funext j a
    change markedMemoryActualParticle hZ history j ((rename j).symm a)=d.particle j a
    simpa only [Equiv.apply_symm_apply] using markedMemoryBandAddressEquiv_particle hZ d order hempty hn j ((rename j).symm a)
  · intro t ht j
    rw [markedMemoryIndependentRelabel_queue,markedMemoryActualTableau_queue hZ history ha t ht j]
    exact markedMemoryBandAddressEquiv_queue hZ d order t ht j

theorem markedMemoryNormalized_reverse_order
    (hempty : ∀ j,((markedMemoryIndependentState hZ d 0 (Nat.zero_le n)).2.2.1.1 j:ℕ)=0)
    (hn : MarkedMemoryBirthNormalized hZ d)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) :
    markedMemoryActualOrder hZ history ha=order := by
  funext v
  apply markedMemoryIndependentSourceSlots_injective hZ d v v.2
  let q := markedMemoryIndependentRelabel hZ rename (markedMemoryActualTableau hZ history ha)
  calc
    _ = markedMemoryIndependentSourceSlots hZ q v v.2 (markedMemoryActualOrder hZ history ha v) :=
      (markedMemoryFinite_eq_sourceSlots hZ q d
        (markedMemoryNormalized_reverse_extraction hZ d order hempty hn ha) v v.2 _).symm
    _ = markedMemoryIndependentSourceSlots hZ (markedMemoryActualTableau hZ history ha) v v.2
        (markedMemoryActualOrder hZ history ha v) :=
      markedMemoryIndependentRelabel_sourceSlots hZ rename (markedMemoryActualTableau hZ history ha) v v.2 _
    _ = markedMemoryHistorySourceSlots hZ history v :=
      (markedMemoryActualOrder_sourceSlots hZ history ha v).trans
        (markedMemoryHistoryVertexEdge_sourceSlots hZ history v)
    _ = _ := markedMemoryIndependentHistory_sourceSlots hZ d order v

end
end ArtinMatthews
