module

public import ArtinMatthews.GiantSignedLifespanMemorySchedule
public import ArtinMatthews.GiantSignedGhostVisitCoefficient
public import ArtinMatthews.GiantSignedChronologicalWeight
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

/-! A decoded lifespan schedule replays each original ordered memory.
Its enumeration certificates are fixed by the actual particle indices. -/

namespace ArtinMatthews
noncomputable section

theorem giantSignedLifespanMemory_eq {P : Finset ℕ} {pending : Finset P}
    {anchor : (p : P) → ZMod p.val} {m : GiantSignedGroupMemory P}
    (a b : GiantSignedLifespanMemory pending anchor m) : a = b := by
  have he : a.enumeration = b.enumeration := by
    apply Equiv.ext
    intro j
    apply Subtype.ext
    exact (congrArg Sigma.fst (a.particle_eq j)).symm.trans (congrArg Sigma.fst (b.particle_eq j))
  cases a
  cases b
  cases he
  rfl

theorem giantSignedLifespanBefore_eq {B : Type*} {P : B → Finset ℕ} {n : ℕ}
    {A : ∀ g, P g → Finset (Fin (n+1))} {c : ∀ g p, GiantSignedResidueLifespanChoice (A g p)}
    {offset : Fin (n+1) → ℤ} {i : Fin (n+1)}
    (a b : GiantSignedLifespanScheduleData.Before (c := c) (offset := offset) i)
    (he : a.1 = b.1) : a = b := by
  rcases a with ⟨m,hm⟩
  rcases b with ⟨m',hm'⟩
  dsimp only at he
  subst m'
  exact congrArg (Sigma.mk m) (funext fun g => giantSignedLifespanMemory_eq (hm g) (hm' g))

private theorem edgeChoice_heq_of_memory {B : Type*} {P : B → Finset ℕ} {n : ℕ}
    {A : ∀ g, P g → Finset (Fin (n+1))} (c : ∀ g p, GiantSignedResidueLifespanChoice (A g p))
    (i : Fin n) (offset : Fin (n+1) → ℤ) {m m' : GiantSignedMemory P} (he : m = m')
    (h : ∀ g, GiantSignedLifespanMemory (giantSignedGhostVisitAfter (c g) i.castSucc)
      (giantSignedLifespanResidue (c g) offset i.castSucc) (giantSignedMemoryGroupEquiv P m g))
    (h' : ∀ g, GiantSignedLifespanMemory (giantSignedGhostVisitAfter (c g) i.castSucc)
      (giantSignedLifespanResidue (c g) offset i.castSucc) (giantSignedMemoryGroupEquiv P m' g))
    {t : B → ℕ} (source target : GiantSignedPrimeTuple P t) (ht : ∀ g, Function.Injective (target g)) :
    HEq (giantSignedLifespanEdgeChoice c i.castSucc i.succ offset m h source target ht)
      (giantSignedLifespanEdgeChoice c i.castSucc i.succ offset m' h' source target ht) := by
  subst m'
  have hc : h = h' := funext fun g => giantSignedLifespanMemory_eq (h g) (h' g)
  rw [hc]

private theorem edgeTarget_eq_of_memory {B : Type*} {P : B → Finset ℕ} {t : B → ℕ}
    (d : ℤ) {m m' : GiantSignedMemory P} (hm : m = m') (source : GiantSignedPrimeTuple P t)
    {r : GiantSignedEdgeChoice t m.1} {r' : GiantSignedEdgeChoice t m'.1} (hr : HEq r r') :
    giantSignedEdgeTarget d m source r = giantSignedEdgeTarget d m' source r' := by
  subst m'
  cases eq_of_heq hr
  rfl

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    {A : ∀ g, PB g → Finset (Fin (n+1))}
    {c : ∀ g p, GiantSignedResidueLifespanChoice (A g p)}
    {offset : Fin (n+1) → ℤ} {q : Fin (n+1) → ℝ}
    (data : GiantSignedLifespanScheduleData c offset q (fun i g => ell+(C i g).card))
    (h : GiantSignedChronologicalChoices PS PB ell C batch)

theorem giantSignedLifespanSchedule_after_replay (v : Fin (n+1))
    (before : ∀ g, GiantSignedLifespanMemory (giantSignedGhostVisitBefore (c g) v)
      (giantSignedLifespanResidue (c g) offset v)
      (giantSignedMemoryGroupEquiv PB (h.state v).2.2 g))
    (hghost : ∀ g, giantSignedFixedGhostMove (h.state v).2.2 (batch v) (h.deleted v) (h.born v) g =
      giantSignedGhostVisitMove (c g) v (giantSignedMemoryGroupEquiv PB (h.state v).2.2 g) (data.birthOrder v g)) :
    data.after v ⟨(h.state v).2.2,before⟩ = giantSignedChronologicalGhostTarget h v := by
  apply congrArg (giantSignedGhostMemoryMoveTarget (h.state v).2.2)
  funext g
  exact (hghost g).symm

theorem giantSignedLifespanSchedule_replays (κ : Fin n → ℤ)
    (hc : GiantSignedChronologicalCompatible κ h) (h0 : (h.state 0).2.2 = giantSignedEmptyMemory PB)
    (before : ∀ v g, GiantSignedLifespanMemory (giantSignedGhostVisitBefore (c g) v)
      (giantSignedLifespanResidue (c g) offset v) (giantSignedMemoryGroupEquiv PB (h.state v).2.2 g))
    (after : ∀ v g, GiantSignedLifespanMemory (giantSignedGhostVisitAfter (c g) v)
      (giantSignedLifespanResidue (c g) offset v)
      (giantSignedMemoryGroupEquiv PB (giantSignedChronologicalGhostTarget h v) g))
    (hghost : ∀ v g, giantSignedFixedGhostMove (h.state v).2.2 (batch v) (h.deleted v) (h.born v) g =
      giantSignedGhostVisitMove (c g) v (giantSignedMemoryGroupEquiv PB (h.state v).2.2 g) (data.birthOrder v g))
    (hSource : ∀ i, data.source i = giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigSource h i))
    (hStep : ∀ i, data.increment i = κ i * (giantSignedChronologicalProduct h i : ℤ))
    (hEdge : ∀ i, h.edge i = giantSignedLifespanEdgeChoice c i.castSucc i.succ offset
      (giantSignedChronologicalGhostTarget h i.castSucc) (after i.castSucc) (data.source i) (data.target i)
      (data.target_injective i)) (v : Fin (n+1)) :
    data.memory v = ⟨(h.state v).2.2,before v⟩ := by
  induction v using Fin.induction with
  | zero => exact giantSignedLifespanBefore_eq _ _ (data.memory_zero.trans h0.symm)
  | succ i ih =>
    rw [data.memory_succ,ih]
    let m : GiantSignedLifespanScheduleData.Before (c := c) (offset := offset) i.castSucc :=
      ⟨(h.state i.castSucc).2.2,before i.castSucc⟩
    have hm := giantSignedLifespanSchedule_after_replay data h i.castSucc (before i.castSucc) (hghost i.castSucc)
    have he : HEq (data.edge i m) (h.edge i) := by
      rw [hEdge i]
      exact edgeChoice_heq_of_memory c i offset hm (data.after_certificate i.castSucc m) (after i.castSucc)
        (data.source i) (data.target i) (data.target_injective i)
    apply giantSignedLifespanBefore_eq
    change giantSignedEdgeTarget (data.increment i) (data.after i.castSucc m) (data.source i) (data.edge i m) = _
    rw [hStep i,hSource i]
    exact (edgeTarget_eq_of_memory _ hm _ he).trans (hc i).2.2.2.1.symm

end
end ArtinMatthews
