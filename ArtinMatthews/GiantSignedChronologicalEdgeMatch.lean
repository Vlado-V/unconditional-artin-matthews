module

public import ArtinMatthews.GiantSignedChronologicalEdgeLifecycle
public import ArtinMatthews.GiantSignedChronologicalMemoryMatch


set_option backward.privateInPublic true
@[expose] public section

/-! The original store and promotion sets and the ordered retrieval
injection are uniquely recovered from the supported prime lifespans. -/

namespace ArtinMatthews
noncomputable section

private theorem edgeChoice_ext {B : Type*} {t d : B → ℕ} (a b : GiantSignedEdgeChoice t d)
    (hs : a.1 = b.1) (ht : a.2.1 = b.2.1)
    (he : ∀ g (j : Fin (a.2.1 g).card), a.2.2 g j =
      b.2.2 g ((finCongr (congrArg (fun T => (T g).card) ht)) j)) : a = b := by
  rcases a with ⟨S,T,e⟩
  rcases b with ⟨S',T',e'⟩
  dsimp only at hs ht he
  subst S'
  subst T'
  have heq : e = e' := funext fun g => Function.Embedding.ext (fun j => he g j)
  rw [heq]

private theorem selected_cast {P : Finset ℕ} {t : ℕ} {S T : Finset (Fin t)}
    (h : S = T) (a : Fin t → P) (j : Fin S.card) :
    giantSignedEdgeSelected S a j = giantSignedEdgeSelected T a ((finCongr (congrArg Finset.card h)) j) := by
  subst T
  rfl

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (κ : Fin n → ℤ)
    {q : Fin (n+1) → ℝ} {A : ∀ g, PB g → Finset (Fin (n+1))}
    (choice : ∀ g p, GiantSignedChronologicalPrimeMatch h κ q g p (A g p))
    (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h))

local notation "Choices" => fun g p => GiantSignedChronologicalPrimeMatch.choice (choice g p)
local notation "Offset" => giantSignedChronologicalOffset κ h

theorem giantSignedChronologicalEdgeMatch_of_prime (i : Fin n)
    (hA : ∀ g p v, v ∈ A g p ↔ GiantSignedChronologicalActive h v g p)
    (hs : ∀ g, Function.Injective (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigSource h i) g))
    (ht : ∀ g, Function.Injective (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i) g)) :
    h.edge i = giantSignedLifespanEdgeChoice Choices i.castSucc i.succ Offset
      (giantSignedChronologicalGhostTarget h i.castSucc)
      (giantSignedChronologicalAfterMemoryMatch h κ choice ha hd i.castSucc)
      (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigSource h i))
      (giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i)) ht := by
  let c := Choices
  let m := giantSignedChronologicalGhostTarget h i.castSucc
  let after := giantSignedChronologicalAfterMemoryMatch h κ choice ha hd i.castSucc
  let source := giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigSource h i)
  let target := giantSignedPatternFreeLabels (C i) (giantSignedChronologicalBigTarget h i)
  let original := h.edge i
  let reconstructed := giantSignedLifespanEdgeChoice c i.castSucc i.succ Offset m after source target ht
  have hStore : original.1 = reconstructed.1 := by
    funext g
    ext j
    change j ∈ (h.edge i).1 g ↔ j ∈ giantSignedLifespanStoreSlots (c g) i.castSucc i.succ (source g)
    rw [giantSignedChronologicalStore_iff_pending h κ ha hd i g (hs g),giantSignedLifespanStoreSlots_mem]
    let p := source g j
    have hActive : GiantSignedChronologicalActive h i.castSucc g p := by
      let slot := giantTwoSidedPatternFreeSlot (C i g) ell (giantSignedPatternFreeSlotEquiv (C i g) ell j)
      exact ⟨h.sourceBigPermutation i g slot,rfl⟩
    have hNotPending : ¬giantSignedPrimePendingAfter (c g p) i.castSucc := fun hp =>
      giantSignedChronologicalPendingAfter_not_active h κ ha hd i.castSucc g p
        (((choice g p).after i.castSucc).mpr hp) hActive
    rw [(choice g p).before i.succ,giantSignedPrimePendingBefore_adjacent (c g p) i.castSucc i.succ rfl]
    simp only [hNotPending,false_and,false_or] <;> rfl
  have hPromote : original.2.1 = reconstructed.2.1 := by
    funext g
    ext j
    change j ∈ (h.edge i).2.1 g ↔ j ∈ giantSignedLifespanPromoteSlots (c g) i.castSucc i.succ (target g)
    rw [giantSignedChronologicalPromote_iff_pending h κ ha hd i g (ht g),giantSignedLifespanPromoteSlots_mem]
    let p := target g j
    have hActive : GiantSignedChronologicalActive h i.succ g p := by
      let slot := giantTwoSidedPatternFreeSlot (C i g) ell (giantSignedPatternFreeSlotEquiv (C i g) ell j)
      exact ⟨h.targetBigPermutation i g slot,rfl⟩
    rw [(choice g p).after i.castSucc,giantSignedPrimePromote]
    exact (and_iff_left ((hA g p i.succ).mpr hActive)).symm
  refine edgeChoice_ext original reconstructed hStore hPromote (fun g j => ?_)
  let he := congrFun hPromote g
  let j' := (finCongr (congrArg Finset.card he)) j
  change original.2.2 g j = reconstructed.2.2 g j'
  apply (after g).prime_injective
  have hOld := congrArg Sigma.fst ((ha.promotion i).1 g j)
  have hNew := congrArg Sigma.fst (giantSignedLifespanRetrieval_particle (c g) i.castSucc i.succ
    (target g) (ht g) Offset (giantSignedMemoryGroupEquiv PB m g) (after g) j')
  exact hOld.trans ((selected_cast he (target g) j).trans hNew.symm)

end
end ArtinMatthews
