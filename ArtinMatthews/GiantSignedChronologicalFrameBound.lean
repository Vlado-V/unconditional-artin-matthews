module

public import ArtinMatthews.GiantSignedChronologicalChoices
public import ArtinMatthews.GiantSignedUniformBirthFrame


set_option backward.privateInPublic true
@[expose] public section

/-! A support condition on actual memories supplies the potential-frame
bound. The chronological state carrier itself retains every degree. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

def GiantSignedChronologicalMemoryCap (H : ℕ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch) : Prop :=
  (∀ i, (∑ g : B, (h.state i).2.2.1 g) ≤ H) ∧
    (∀ i, (∑ g : B, (giantSignedChronologicalGhostTarget h i).1 g) ≤ H)

omit [Fintype B] in
theorem giantSignedChronological_batch_le_degree
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (i : Fin (n+1)) (g : B) :
    batch i g ≤ (giantSignedChronologicalGhostTarget h i).1 g := by
  change batch i g ≤
    (giantSignedFixedGhostTarget (h.state i).2.2 (batch i) (h.deleted i) (h.born i)).1 g
  rw [giantSignedFixedGhostTarget_degree]
  omega

theorem giantSignedChronologicalMemoryCap_batches (H : ℕ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (hcap : GiantSignedChronologicalMemoryCap H h) : ∀ i g, batch i g ≤ H := by
  intro i g
  have hs : (giantSignedChronologicalGhostTarget h i).1 g ≤
      ∑ j : B, (giantSignedChronologicalGhostTarget h i).1 j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
  exact (giantSignedChronological_batch_le_degree h i g).trans (hs.trans (hcap.2 i))

theorem giantSignedChronologicalMemoryCap_birthGuard (H : ℕ)
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (hcap : GiantSignedChronologicalMemoryCap H h) :
    GiantSignedBirthDistinct (giantSignedChronologicalBirthData h) ↔
      MarkedPerformedInjective (giantSignedUniformBirthValue
        (giantSignedChronologicalBirthData h) H
        (giantSignedChronologicalMemoryCap_batches H h hcap)) :=
  giantSignedBirthDistinct_iff_uniform _ _ _

end
end ArtinMatthews
