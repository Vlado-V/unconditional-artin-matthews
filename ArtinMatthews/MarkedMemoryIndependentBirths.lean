module

public import ArtinMatthews.MarkedMemoryIndependentEdge
public import ArtinMatthews.MarkedMemoryHistoryBirthIndices
public import ArtinMatthews.MarkedMemoryIndependentPopulation
public import ArtinMatthews.MarkedMemoryLifespanSlotExchange
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

/-! Genuine first times for the reconstructed births. Active exchange
and interval incidence force every unpromoted incoming identity to begin
on that edge; the statement is derived rather than assumed as a
history/address bijection. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

theorem markedMemoryIndependentIncoming_not_active (v : ℕ) (hv : v < n) (j : J) :
    ¬ (d.lifespan j).active (2*v+1) ((d.lifespan j).incoming (2*v+1)) := by
  have hn := markedMemoryActiveExchange_incoming_not_source (d.activeId v j) (d.activeId (v+1) j)
    (markedMemoryIndependentOutgoing hZ d v hv j) (markedMemoryIndependentIncoming hZ d v hv j)
    (markedMemoryIndependentActive_exchange hZ d v hv j) (by
      rw [markedMemoryIndependentOutgoing_eq, markedMemoryIndependentIncoming_eq]
      exact ((d.lifespan j).edge_distinct (2*v+1) (by omega) (by omega)).symm)
  intro ha
  obtain ⟨i,hi⟩ := (markedMemoryIndependentActive_mem hZ d (2*v+1) (by omega) j _).mp ha
  have he : (2*v+1)/2 = v := by omega
  rw [he] at hi
  exact hn ⟨i,hi.trans (markedMemoryIndependentIncoming_eq hZ d v hv j).symm⟩

theorem markedMemoryIndependentIncoming_first (v : ℕ) (hv : v < n) (j : J)
    (hfresh : (d.lifespan j).incoming (2*v+1) ∉ markedMemoryIndependentQueue hZ d (2*v+1) j) :
    (d.lifespan j).first ((d.lifespan j).incoming (2*v+1)) = (2*v+1)+1 := by
  have ha := d.active_alive (v+1) hv j (markedMemoryIndependentIncoming hZ d v hv j)
  rw [markedMemoryIndependentIncoming_eq] at ha
  have hn := markedMemoryIndependentIncoming_not_active hZ d v hv j
  have hnot : ¬ (d.lifespan j).first ((d.lifespan j).incoming (2*v+1)) ≤ 2*v+1 := by
    intro hf
    apply hfresh
    apply (markedMemoryPendingQueueAt_mem (d.lifespan j) (2*v+1) (by omega) _).mpr
    exact ⟨hf,by omega,hn⟩
  omega

def markedMemoryIndependentGhostBirthLabel (v : ℕ) (hv : v ≤ n) :
    MarkedMemoryGhostBirthIndex (markedMemoryIndependentGhost hZ d v hv) ↪ Σ j, A j :=
  Function.Embedding.sigmaMap (Function.Embedding.refl J) (fun j =>
    markedMemoryQueueEmbedding ((d.lifespan j).births (2*v))
      ((d.lifespan j).ghost_nodup (2*v) (by omega) (by omega)))

theorem markedMemoryIndependentGhostBirth_first (v : ℕ) (hv : v ≤ n)
    (b : MarkedMemoryGhostBirthIndex (markedMemoryIndependentGhost hZ d v hv)) :
    (d.lifespan (markedMemoryIndependentGhostBirthLabel hZ d v hv b).1).first
      (markedMemoryIndependentGhostBirthLabel hZ d v hv b).2 = 2*v+1 :=
  ((d.lifespan b.1).ghost_births (2*v) (by omega) (by omega) _).mp (List.get_mem _ b.2) |>.1

def markedMemoryIndependentEdgeBirthLabel (v : ℕ) (hv : v < n) (order : J → Equiv.Perm (Fin pads)) :
    MarkedMemoryEdgeBirthIndex (markedMemoryIndependentEdge hZ d v hv order) ↪ Σ j, A j where
  toFun b := ⟨b.1,(d.lifespan b.1).incoming (2*v+1)⟩
  inj' := by
    intro a b hab
    exact Subtype.ext (congrArg Sigma.fst hab)

theorem markedMemoryIndependentEdgeBirth_first (v : ℕ) (hv : v < n) (order : J → Equiv.Perm (Fin pads))
    (b : MarkedMemoryEdgeBirthIndex (markedMemoryIndependentEdge hZ d v hv order)) :
    (d.lifespan (markedMemoryIndependentEdgeBirthLabel hZ d v hv order b).1).first
      (markedMemoryIndependentEdgeBirthLabel hZ d v hv order b).2 = (2*v+1)+1 := by
  apply markedMemoryIndependentIncoming_first hZ d v hv b.1
  intro hm
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp hm
  have hp := (markedMemoryEdgeQueuePromotion_eq_some
    (markedMemoryIndependentQueue hZ d (2*v+1))
    (markedMemoryIndependentQueue_nodup hZ d (2*v+1) (by omega))
    (fun j => (d.lifespan j).incoming (2*v+1)) b.1 k).mpr hk
  have hn := b.2
  change markedMemoryEdgeQueuePromotion (markedMemoryIndependentQueue hZ d (2*v+1))
    (markedMemoryIndependentQueue_nodup hZ d (2*v+1) (by omega))
    (fun j => (d.lifespan j).incoming (2*v+1)) b.1 = none at hn
  rw [hp] at hn
  cases hn

end
end ArtinMatthews
