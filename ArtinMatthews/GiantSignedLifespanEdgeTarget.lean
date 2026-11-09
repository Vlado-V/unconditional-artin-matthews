module

public import ArtinMatthews.GiantSignedLifespanEdgeResidue
public import ArtinMatthews.GiantSignedLifespanEdgeSupport
public import ArtinMatthews.GiantSignedGhostMemoryCoordinates
public import ArtinMatthews.GiantSignedEdgeStorePromote


set_option backward.privateInPublic true
@[expose] public section

/-! The exact grouped store and retrieval choice reconstructs the
ordered pending memory at the next visit. -/
namespace ArtinMatthews
noncomputable section

variable {B : Type*} {P : B → Finset ℕ} {n : ℕ} {t : B → ℕ}
    {A : ∀ g, P g → Finset (Fin n)}
    (c : ∀ g p, GiantSignedResidueLifespanChoice (A g p)) (v w : Fin n)
    (offset : Fin n → ℤ) (m : GiantSignedMemory P)
    (hm : ∀ g, GiantSignedLifespanMemory (giantSignedGhostVisitAfter (c g) v)
      (giantSignedLifespanResidue (c g) offset v) (giantSignedMemoryGroupEquiv P m g))
    (source target : GiantSignedPrimeTuple P t)
    (htarget : ∀ g, Function.Injective (target g))

def giantSignedLifespanEdgeChoice : GiantSignedEdgeChoice t m.1 :=
  ⟨fun g => giantSignedLifespanStoreSlots (c g) v w (source g),
    fun g => giantSignedLifespanPromoteSlots (c g) v w (target g),
    fun g => giantSignedLifespanRetrieval (c g) v w (target g) (htarget g) offset
      (giantSignedMemoryGroupEquiv P m g) (hm g)⟩

theorem giantSignedLifespanEdgeChoice_hits (q : Fin n → ℝ) (d : ℤ) (hd : offset w = offset v+d)
    (hweight : ∀ g p, giantSignedResidueLifespanWeight p.val offset q (A g p) (c g p) ≠ 0) :
    GiantSignedEdgeHits d m target (giantSignedLifespanEdgeChoice c v w offset m hm source target htarget) :=
  fun g i => giantSignedLifespanRetrieval_hit (c g) offset q hd (hweight g) (target g) (htarget g)
    (giantSignedMemoryGroupEquiv P m g) (hm g) i

theorem giantSignedLifespanEdgeChoice_promotionBan (D : ℕ)
    (hTarget : ∀ g i, ¬ (target g i).val ∣ D) :
    GiantSignedEdgePromotionBan D (giantSignedLifespanEdgeChoice c v w offset m hm source target htarget).2.1 target :=
  fun g i => hTarget g ((giantSignedLifespanPromoteSlots (c g) v w (target g)).orderEmbOfFin rfl i)

def giantSignedLifespanEdgeTarget_memory (q : Fin n → ℝ) (d : ℤ) (hd : offset w = offset v+d)
    (hAdj : v.val+1 = w.val)
    (hweight : ∀ g p, giantSignedResidueLifespanWeight p.val offset q (A g p) (c g p) ≠ 0)
    (hsource : ∀ g, Function.Injective (source g))
    (hSourceCover : ∀ g p, v ∈ A g p → w ∉ A g p → ∃ j, source g j = p)
    (hTargetCover : ∀ g p, w ∈ A g p → v ∉ A g p → ∃ j, target g j = p)
    (g : B) :
    GiantSignedLifespanMemory (giantSignedGhostVisitBefore (c g) w)
      (giantSignedLifespanResidue (c g) offset w)
      (giantSignedMemoryGroupEquiv P (giantSignedEdgeTarget d m source
        (giantSignedLifespanEdgeChoice c v w offset m hm source target htarget)) g) := by
  classical
  let choice := giantSignedLifespanEdgeChoice c v w offset m hm source target htarget
  let R := giantSignedEdgeRetrievedIndices choice g
  let S := choice.1 g
  let oldIndex := (Rᶜ).orderEmbOfFin rfl
  let old (j : Fin (Rᶜ).card) := (m.2 g (oldIndex j)).1
  let store (j : Fin S.card) := giantSignedEdgeSelected S (source g) j
  have hR (j : Fin (m.1 g)) : j ∈ R ↔ w ∈ A g (m.2 g j).1 :=
    giantSignedLifespanRetrieved_mem (c g) v w offset (giantSignedMemoryGroupEquiv P m g)
      (hm g) (target g) (htarget g) (hTargetCover g) j
  have ho (j : Fin (Rᶜ).card) : giantSignedPrimePendingAfter (c g (old j)) v ∧ w ∉ A g (old j) := by
    refine ⟨(mem_giantSignedGhostVisitAfter (c g) v _).mp ((hm g).prime_mem (oldIndex j)), ?_⟩
    exact fun h => (Finset.mem_compl.mp (Finset.orderEmbOfFin_mem _ rfl j)) ((hR _).mpr h)
  have hs (j : Fin S.card) : giantSignedPrimeStore (c g (store j)) v w :=
    (giantSignedLifespanStoreSlots_mem (c g) v w (source g) _).mp (Finset.orderEmbOfFin_mem S rfl j)
  let targetIndex : Fin (Rᶜ).card ⊕ Fin S.card → ↥(giantSignedGhostVisitBefore (c g) w) :=
    fun j => ⟨Sum.elim old store j, (mem_giantSignedGhostVisitBefore (c g) w _).mpr
      ((giantSignedPrimePendingBefore_adjacent (c g (Sum.elim old store j)) v w hAdj).mpr
        (by cases j with
            | inl i => exact Or.inl (ho i)
            | inr i => exact Or.inr (hs i)))⟩
  have hinj : Function.Injective targetIndex := by
    have hp : Function.Injective (Sum.elim old store) := Sum.elim_injective.mpr
      ⟨(hm g).prime_injective.comp oldIndex.injective, (hsource g).comp (S.orderEmbOfFin rfl).injective,
        fun i j he => giantSignedPrimeSurviveStore_disjoint (c g (store j)) v w ⟨he ▸ ho i, hs j⟩⟩
    exact fun _ _ h => hp (congrArg Subtype.val h)
  have hsurj : Function.Surjective targetIndex := by
    intro p
    rcases (giantSignedPrimePendingBefore_adjacent (c g p.val) v w hAdj).mp
        ((mem_giantSignedGhostVisitBefore (c g) w p.val).mp p.property) with ha | ha
    · let p' : ↥(giantSignedGhostVisitAfter (c g) v) :=
        ⟨p.val,(mem_giantSignedGhostVisitAfter (c g) v p.val).mpr ha.1⟩
      let j := (hm g).index p'
      have hj : (m.2 g j).1 = p.val := (hm g).index_prime p'
      have hj' : j ∈ Rᶜ := Finset.mem_compl.mpr (fun ht => ha.2 (hj ▸ (hR j).mp ht))
      have hrange : j ∈ Set.range oldIndex := by
        change j ∈ Set.range ((Rᶜ).orderEmbOfFin rfl)
        rw [Finset.range_orderEmbOfFin]
        exact hj'
      obtain ⟨i,hi⟩ := hrange
      exact ⟨.inl i, Subtype.ext ((congrArg (fun j => (m.2 g j).1) hi).trans hj)⟩
    · obtain ⟨i,hi⟩ := giantSignedLifespanStoreSelected_surjective (c g) v w
        (source g) (hSourceCover g) ha
      exact ⟨.inr i, Subtype.ext hi⟩
  let e := Equiv.ofBijective targetIndex ⟨hinj,hsurj⟩
  let anchored (p : P g) : GiantSignedParticle (P g) := ⟨p,giantSignedLifespanResidue (c g) offset w p⟩
  refine ⟨finSumFinEquiv.symm.trans e, ?_⟩
  intro j
  change Fin ((Rᶜ).card + S.card) at j
  refine Fin.addCases ?_ ?_ j
  · intro i
    have hi := giantSignedEdgeTarget_survivor d m source choice g i
    have hmem := (hm g).particle_anchor (oldIndex i)
    have htranslate := giantSignedLifespanResidue_translate (c g) offset hd (old i) (ho i).1
    exact hi.trans ((congrArg (giantSignedParticleTranslate d) hmem).trans
      (htranslate.trans (by
        change anchored (old i) = anchored (e (finSumFinEquiv.symm (Fin.castAdd S.card i))).val
        rw [finSumFinEquiv_symm_apply_castAdd]
        rfl)))
  · intro i
    have hi := giantSignedEdgeTarget_store d m source choice g i
    have hstore := giantSignedLifespanStore_particle (c g) offset q hd (store i) (hweight g _)
      (giantSignedPrimeStore_active (c g) v w (hs i)).1
    exact hi.trans (hstore.trans (by
      change anchored (store i) = anchored (e (finSumFinEquiv.symm (Fin.natAdd (Rᶜ).card i))).val
      rw [finSumFinEquiv_symm_apply_natAdd]
      rfl))

end
end ArtinMatthews
