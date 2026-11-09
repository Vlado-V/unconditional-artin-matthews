module

public import ArtinMatthews.MarkedMinorArcRawEdgeSymmetryChoices


set_option backward.privateInPublic true
@[expose] public section

/-! Literal promoted-old survivor transport, with source stores appended
unchanged at their actual source anchors. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem markedRawEdgePromotion_mem_reindex {k k' : ℕ} (e : Fin k' ≃ Fin k)
    (p : Option (Fin k)) (i : Fin k') :
    e i ∈ p.toFinset ↔ i ∈ (p.map e.symm).toFinset := by
  cases p <;> simp [Equiv.eq_symm_apply]

def markedRawEdgeSurvivorSubsetEquiv {k k' : ℕ} (e : Fin k' ≃ Fin k)
    (p : Option (Fin k)) :
    ↥(Finset.univ \ (p.map e.symm).toFinset) ≃ ↥(Finset.univ \ p.toFinset) where
  toFun i := ⟨e i.1,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
    (Finset.mem_sdiff.mp i.2).2 ((markedRawEdgePromotion_mem_reindex e p i.1).mp h)⟩⟩
  invFun i := ⟨e.symm i.1,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => by
    have hh := (markedRawEdgePromotion_mem_reindex e p (e.symm i.1)).mpr h
    exact (Finset.mem_sdiff.mp i.2).2 (by simpa only [Equiv.apply_symm_apply] using hh)⟩⟩
  left_inv i := by ext; simp
  right_inv i := by ext; simp

def markedRawEdgeSurvivorIndexEquiv {k k' : ℕ} (e : Fin k' ≃ Fin k)
    (p : Option (Fin k)) :
    Fin (Finset.univ \ (p.map e.symm).toFinset).card ≃ Fin (Finset.univ \ p.toFinset).card :=
  ((Finset.univ \ (p.map e.symm).toFinset).orderIsoOfFin rfl).toEquiv.trans
    ((markedRawEdgeSurvivorSubsetEquiv e p).trans
      ((Finset.univ \ p.toFinset).orderIsoOfFin rfl).toEquiv.symm)

theorem markedRawEdgeSurvivorIndexEquiv_apply {k k' : ℕ} (e : Fin k' ≃ Fin k)
    (p : Option (Fin k)) (i : Fin (Finset.univ \ (p.map e.symm).toFinset).card) :
    (Finset.univ \ p.toFinset).orderEmbOfFin rfl (markedRawEdgeSurvivorIndexEquiv e p i)=
      e ((Finset.univ \ (p.map e.symm).toFinset).orderEmbOfFin rfl i) := by
  exact congrArg Subtype.val (((Finset.univ \ p.toFinset).orderIsoOfFin rfl).toEquiv.apply_symm_apply
    (markedRawEdgeSurvivorSubsetEquiv e p (((Finset.univ \ (p.map e.symm).toFinset).orderIsoOfFin rfl) i)))

/-- Specialization of the genuine choice equivalence to the source's
literal pending-index permutation, fixing position and active slots. -/
abbrev markedRawEdgeChoicePermute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (a : MarkedRawActive P (pads+1))
    (m : MarkedRawMemory P B) (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ))) :
    MarkedRawEdgeChoice hZ (z,(a,m)) ≃
      MarkedRawEdgeChoice hZ (z,(a,markedRawMemoryPermute m σ)) :=
  markedRawEdgeChoiceReindexEquiv hZ (z,(a,m)) (z,(a,markedRawMemoryPermute m σ)) σ (fun _ _ => rfl)

theorem markedRawEdgeChoicePermute_targetLast {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (a : MarkedRawActive P (pads+1))
    (m : MarkedRawMemory P B) (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ)))
    (c : MarkedRawEdgeChoice hZ (z,(a,m))) :
    markedRawEdgeTargetLast (markedRawMemoryPermute m σ)
      (markedRawEdgeChoicePermute hZ z a m σ c).promotions
      (markedRawEdgeChoicePermute hZ z a m σ c).fresh =
      markedRawEdgeTargetLast m c.promotions c.fresh :=
  markedRawEdgeChoiceReindex_targetLast hZ (z,(a,m))
    (z,(a,markedRawMemoryPermute m σ)) σ (fun _ _ => rfl) c

theorem markedRawEdgeTargetMemory_symmetric_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (a : MarkedRawActive P (pads+1))
    (m : MarkedRawMemory P B) (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ)))
    (f : MarkedRawMemory P B → ℂ) (hf : MarkedRawMemorySymmetric f)
    (c : MarkedRawEdgeChoice hZ (z,(a,m))) :
    f (markedRawEdgeTargetMemory hZ (z,(a,markedRawMemoryPermute m σ))
      (markedRawEdgeChoicePermute hZ z a m σ c)) =
      f (markedRawEdgeTargetMemory hZ (z,(a,m)) c) := by
  apply markedRawMemorySymmetric_equiv hf
    (markedRawEdgeTargetMemory hZ (z,(a,m)) c) _
    (fun j => markedRawGhostAppendIndexEquiv (l := if c.store j then 1 else 0)
      (markedRawEdgeSurvivorIndexEquiv (σ j) (c.promotions j)))
  intro j i
  dsimp only [markedRawEdgeTargetMemory, markedRawGhostTargetMemory]
  apply markedRawGhostAppendIndexEquiv_values
  intro k
  exact congrArg (m.2 j) (markedRawEdgeSurvivorIndexEquiv_apply (σ j) (c.promotions j) k).symm

theorem markedRawEdgeTargetState_symmetric_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (a : MarkedRawActive P (pads+1))
    (m : MarkedRawMemory P B) (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ)))
    (f : MarkedRawState P (pads+1) B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m))))
    (c : MarkedRawEdgeChoice hZ (z,(a,m))) :
    f (markedRawEdgeTargetState hZ (z,(a,markedRawMemoryPermute m σ))
      (markedRawEdgeChoicePermute hZ z a m σ c)) =
      f (markedRawEdgeTargetState hZ (z,(a,m)) c) := by
  have hl := markedRawEdgeChoicePermute_targetLast hZ z a m σ c
  change f (c.target,((markedRawActiveSplit pads).symm
      (((markedRawActiveSplit pads) a).1,
        markedRawEdgeTargetLast (markedRawMemoryPermute m σ)
          (markedRawEdgeChoicePermute hZ z a m σ c).promotions
          (markedRawEdgeChoicePermute hZ z a m σ c).fresh),_)) = _
  rw [hl]
  exact markedRawEdgeTargetMemory_symmetric_permute hZ z a m σ
    (fun mem => f (c.target,((markedRawActiveSplit pads).symm
      (((markedRawActiveSplit pads) a).1,markedRawEdgeTargetLast m c.promotions c.fresh),mem)))
    (hf _ _) c

theorem markedRawEdgeTargetMemory_pendingHits_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (z : Z) (a : MarkedRawActive P (pads+1))
    (m : MarkedRawMemory P B) (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ)))
    (c : MarkedRawEdgeChoice hZ (z,(a,m))) (v : ℤ × ℤ) (hv : IsCoprime v.1 v.2) :
    markedRawPendingHits (markedRawEdgeTargetMemory hZ (z,(a,markedRawMemoryPermute m σ))
      (markedRawEdgeChoicePermute hZ z a m σ c)) v hv =
      markedRawPendingHits (markedRawEdgeTargetMemory hZ (z,(a,m)) c) v hv := by
  have hh := markedRawEdgeTargetMemory_symmetric_permute hZ z a m σ
    (fun mem => (markedRawPendingHits mem v hv : ℂ))
    (fun mem τ => congrArg (fun n : ℕ => (n : ℂ)) (markedRawPendingHits_permute mem τ v hv)) c
  exact_mod_cast hh

end ArtinMatthews
