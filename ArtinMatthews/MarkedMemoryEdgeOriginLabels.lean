module

public import ArtinMatthews.MarkedMemoryHistorySlotOrigins
public import ArtinMatthews.MarkedMemoryPopulationTransport
public import ArtinMatthews.MarkedMemoryLifespanGhostQueue
public import ArtinMatthews.MarkedMemoryHistoryEdgeOrigins
public import ArtinMatthews.MarkedMemoryHistoryEdgeOriginsPrime
public import ArtinMatthews.MarkedMemoryQueueOriginLabels
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

/-! Abstract identity labels through the actual canonical edge origin.
Only a promoted incoming identity must equal its selected old pending
identity. Copies and stores preserve their source identity literally. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {A : J → Type*} {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
  (c : MarkedRawEdgeChoice hZ s)
  (activeId : (j : J) → Fin (pads+1) → A j)
  (pendingId : (j : J) → Fin (s.2.2.1.1 j : ℕ) → A j) (incoming : (j : J) → A j)

def markedMemoryEdgeTargetGroupLabel (j : J) :
    (Fin (pads+1) ⊕ Fin ((markedRawEdgeTargetMemory hZ s c).1.1 j : ℕ)) → A j :=
  Sum.elim (Fin.lastCases (incoming j) (fun k => activeId j k.castSucc))
    (Fin.append
      (fun k => pendingId j ((markedRawGhostSurvivors s.2.2
        (markedRawEdgePromotionDeletion c.promotions) j).orderEmbOfFin rfl k))
      (fun _ => activeId j (Fin.last pads)))

theorem markedMemoryEdgeTargetGroupLabel_active (j : J) (k : Fin (pads+1)) :
    markedMemoryEdgeTargetGroupLabel hZ s c activeId pendingId incoming j (Sum.inl k) =
      Fin.lastCases (motive := fun _ : Fin (pads+1) => A j) (incoming j)
        (fun k => activeId j k.castSucc) k := rfl

theorem markedMemoryEdgeTargetGroupLabel_pending_list (j : J) :
    List.ofFn (fun k => markedMemoryEdgeTargetGroupLabel hZ s c activeId pendingId incoming j (Sum.inr k)) =
      List.ofFn (fun k => pendingId j ((markedRawGhostSurvivors s.2.2
        (markedRawEdgePromotionDeletion c.promotions) j).orderEmbOfFin rfl k)) ++
      List.ofFn (fun _ : Fin (if c.store j then 1 else 0) => activeId j (Fin.last pads)) := by
  change List.ofFn (Fin.append
    (fun k : Fin (markedRawGhostSurvivors s.2.2 (markedRawEdgePromotionDeletion c.promotions) j).card =>
      pendingId j ((markedRawGhostSurvivors s.2.2 (markedRawEdgePromotionDeletion c.promotions) j).orderEmbOfFin rfl k))
    (fun _ : Fin (if c.store j then 1 else 0) => activeId j (Fin.last pads))) = _
  exact List.ofFn_fin_append _ _

theorem markedMemoryEdgeGroupOrigin_label
    (hprom : ∀ j k, c.promotions j = some k → pendingId j k = incoming j)
    (j : J) (i : Fin (pads+1) ⊕ Fin ((markedRawEdgeTargetMemory hZ s c).1.1 j : ℕ)) :
    Sum.elim (Sum.elim (activeId j) (pendingId j)) (fun _ => incoming j)
      (markedMemoryEdgeGroupOrigin hZ s c j i) =
        markedMemoryEdgeTargetGroupLabel hZ s c activeId pendingId incoming j i := by
  rcases i with i | i
  · refine Fin.lastCases ?_ (fun k => ?_) i
    · by_cases hn : c.promotions j = none
      · rw [markedMemoryEdgeGroupOrigin_last_none hZ s c j hn]
        change incoming j = Fin.lastCases (incoming j) (fun k => activeId j k.castSucc) (Fin.last pads)
        rw [Fin.lastCases_last]
      · obtain ⟨k,hk⟩ := Option.ne_none_iff_exists'.mp hn
        rw [markedMemoryEdgeGroupOrigin_last_some hZ s c j k hk]
        change pendingId j k = Fin.lastCases (incoming j) (fun k => activeId j k.castSucc) (Fin.last pads)
        rw [Fin.lastCases_last]
        exact hprom j k hk
    · rw [markedMemoryEdgeGroupOrigin_copied]
      change activeId j k.castSucc = Fin.lastCases (incoming j) (fun k => activeId j k.castSucc) k.castSucc
      rw [Fin.lastCases_castSucc]
  · obtain ⟨o,rfl⟩ := (markedMemoryGhostOrigin s.2.2
      (markedRawEdgePromotionDeletion c.promotions) (markedRawEdgeStoreSizes hZ s c) j).symm.surjective i
    cases o with
    | inl old =>
      rw [markedMemoryEdgeGroupOrigin_survivor]
      change pendingId j old.1 = Fin.addCases
        (fun k => pendingId j ((markedRawGhostSurvivors s.2.2
          (markedRawEdgePromotionDeletion c.promotions) j).orderEmbOfFin rfl k))
        (fun _ => activeId j (Fin.last pads))
        (Fin.castAdd (if c.store j then 1 else 0)
          (((markedRawGhostSurvivors s.2.2 (markedRawEdgePromotionDeletion c.promotions) j).orderIsoOfFin rfl).symm old))
      rw [Fin.addCases_left]
      apply congrArg (pendingId j)
      exact (congrArg Subtype.val
        (((markedRawGhostSurvivors s.2.2 (markedRawEdgePromotionDeletion c.promotions) j).orderIsoOfFin rfl).apply_symm_apply old)).symm
    | inr stored =>
      rw [markedMemoryEdgeGroupOrigin_store]
      change activeId j (Fin.last pads) = Fin.addCases
        (fun k => pendingId j ((markedRawGhostSurvivors s.2.2
          (markedRawEdgePromotionDeletion c.promotions) j).orderEmbOfFin rfl k))
        (fun _ => activeId j (Fin.last pads))
        (Fin.natAdd (markedRawGhostSurvivors s.2.2 (markedRawEdgePromotionDeletion c.promotions) j).card stored)
      rw [Fin.addCases_right]

def markedMemoryEdgeSourceLabel : MarkedMemoryPopulationIndex s → Σ j, A j :=
  Sum.elim (fun a => ⟨a.1,activeId a.1 a.2⟩) (fun a => ⟨a.1,pendingId a.1 a.2⟩)

def markedMemoryEdgeFreshLabel : {j : J // c.promotions j = none} → Σ j, A j :=
  fun a => ⟨a.1,incoming a.1⟩

def markedMemoryEdgeTargetLabel : MarkedMemoryPopulationIndex (markedRawEdgeTargetState hZ s c) → Σ j, A j :=
  Sum.elim
    (fun a => ⟨a.1,markedMemoryEdgeTargetGroupLabel hZ s c activeId pendingId incoming a.1 (Sum.inl a.2)⟩)
    (fun a => ⟨a.1,markedMemoryEdgeTargetGroupLabel hZ s c activeId pendingId incoming a.1 (Sum.inr a.2)⟩)

theorem markedMemoryEdgePopulationOrigin_label
    (hprom : ∀ j k, c.promotions j = some k → pendingId j k = incoming j)
    (i : MarkedMemoryPopulationIndex (markedRawEdgeTargetState hZ s c)) :
    Sum.elim (markedMemoryEdgeSourceLabel s activeId pendingId) (markedMemoryEdgeFreshLabel hZ s c incoming)
      (markedMemoryEdgePopulationOrigin hZ s c i) =
        markedMemoryEdgeTargetLabel hZ s c activeId pendingId incoming i := by
  rcases i with ⟨j,k⟩ | ⟨j,k⟩
  · rw [markedMemoryEdgePopulationOrigin_active]
    have h := congrArg (Sigma.mk j) (markedMemoryEdgeGroupOrigin_label hZ s c activeId pendingId incoming hprom j (Sum.inl k))
    generalize ho : markedMemoryEdgeGroupOrigin hZ s c j (Sum.inl k) = o at h ⊢
    rcases o with (old | old) | fresh <;> exact h
  · erw [markedMemoryEdgePopulationOrigin_pending hZ s c j k]
    have h := congrArg (Sigma.mk j) (markedMemoryEdgeGroupOrigin_label hZ s c activeId pendingId incoming hprom j (Sum.inr k))
    generalize ho : markedMemoryEdgeGroupOrigin hZ s c j (Sum.inr k) = o at h ⊢
    rcases o with (old | old) | fresh <;> exact h

theorem markedMemoryEdgeSourceLabel_slots (σ : J → Equiv.Perm (Fin (pads+1)))
    (i : MarkedMemoryPopulationIndex (markedRawSlotEquiv σ s)) :
    markedMemoryEdgeSourceLabel s activeId pendingId (markedMemorySlotPopulationEquiv σ s i) =
      markedMemoryEdgeSourceLabel (markedRawSlotEquiv σ s) (fun j k => activeId j (σ j k)) pendingId i := by
  rcases i with ⟨j,k⟩ | ⟨j,k⟩ <;> rfl

theorem markedMemoryEdgeTargetLabel_cast
    (z' : Z) (active' : MarkedRawActive P (pads+1))
    (ids' : (j : J) → Fin (pads+1) → A j) (queue' : (j : J) → List (A j))
    (particle : (j : J) → A j → MarkedRawParticle (P j)) (hbound : (∑ j, (queue' j).length) ≤ B)
    (hactive : ∀ j k, markedMemoryEdgeTargetGroupLabel hZ s c activeId pendingId incoming j (Sum.inl k) = ids' j k)
    (hpending : ∀ j, List.ofFn (fun k => markedMemoryEdgeTargetGroupLabel hZ s c activeId pendingId incoming j (Sum.inr k)) = queue' j)
    (hstate : markedRawEdgeTargetState hZ s c = (z',(active',markedMemoryLabeledQueueState queue' particle hbound)))
    (i : MarkedMemoryPopulationIndex (markedRawEdgeTargetState hZ s c)) :
    markedMemoryEdgeSourceLabel (z',(active',markedMemoryLabeledQueueState queue' particle hbound))
      ids' (fun j => (queue' j).get) (markedMemoryPopulationStateCast hstate i) =
        markedMemoryEdgeTargetLabel hZ s c activeId pendingId incoming i := by
  rcases i with ⟨j,k⟩ | ⟨j,k⟩
  · rw [markedMemoryPopulationStateCast_active]
    exact congrArg (Sigma.mk j) (hactive j k).symm
  · rw [markedMemoryPopulationStateCast_pending]
    let index : Fin (queue' j).length := Fin.cast
      (congrArg (fun r : MarkedRawState P (pads+1) B Z => (r.2.2.1.1 j : ℕ)) hstate) k
    change (⟨j,(queue' j).get index⟩ : Σ j, A j) =
      ⟨j,markedMemoryEdgeTargetGroupLabel hZ s c activeId pendingId incoming j (Sum.inr k)⟩
    apply congrArg (Sigma.mk j)
    exact (markedMemoryListGet_ofFn_eq _ _ (hpending j) index).trans
      (congrArg (fun k => markedMemoryEdgeTargetGroupLabel hZ s c activeId pendingId incoming j (Sum.inr k))
        (Fin.ext rfl))

end
end ArtinMatthews
