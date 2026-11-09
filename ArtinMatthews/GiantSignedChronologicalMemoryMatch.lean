module

public import ArtinMatthews.GiantSignedChronologicalPrimeMatch
public import ArtinMatthews.GiantSignedChronologicalLifespanLocalCoefficient


set_option backward.privateInPublic true
@[expose] public section

/-! Reconstruct the exact old-index enumerations and the original
ordered ghost batches from the decoded prime choices. -/

namespace ArtinMatthews
noncomputable section

private def lifespanMemoryOfPrimeMembership {P : Finset ℕ} (m : GiantSignedGroupMemory P)
    (s : Finset P) (anchor : (p : P) → ZMod p.val)
    (hrange : ∀ p, p ∈ s ↔ ∃ j, (m.2 j).1 = p)
    (hinj : Function.Injective (fun j => (m.2 j).1))
    (hparticle : ∀ j, m.2 j = ⟨(m.2 j).1,anchor (m.2 j).1⟩) : GiantSignedLifespanMemory s anchor m := by
  let f (j : Fin m.1) : ↥s := ⟨(m.2 j).1,(hrange _).mpr ⟨j,rfl⟩⟩
  let e := Equiv.ofBijective f ⟨fun _ _ h => hinj (congrArg Subtype.val h),fun p => by
    obtain ⟨j,hj⟩ := (hrange p.val).mp p.property
    exact ⟨j,Subtype.ext hj⟩⟩
  exact ⟨e,hparticle⟩

private theorem tuple_heq_of_cast {P : Type*} {b c : ℕ} (h : b = c)
    (x : Fin b → P) (y : Fin c → P) (he : ∀ j, x ((finCongr h.symm) j) = y j) : HEq x y := by
  subst c
  exact heq_of_eq (funext he)

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (κ : Fin n → ℤ)
    {q : Fin (n+1) → ℝ} {A : ∀ g, PB g → Finset (Fin (n+1))}
    (choice : ∀ g p, GiantSignedChronologicalPrimeMatch h κ q g p (A g p))

local notation "Choices" => fun g p => GiantSignedChronologicalPrimeMatch.choice (choice g p)
local notation "Offset" => giantSignedChronologicalOffset κ h

variable (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h))

include ha hd in
def giantSignedChronologicalBeforeMemoryMatch (i : Fin (n+1)) (g : B) :
    GiantSignedLifespanMemory (giantSignedGhostVisitBefore (Choices g) i)
      (giantSignedLifespanResidue (Choices g) Offset i)
      (giantSignedMemoryGroupEquiv PB (h.state i).2.2 g) := by
  refine lifespanMemoryOfPrimeMembership _ _ _ (fun p => ?_) (fun j l he => ?_) (fun j => ?_)
  · exact (mem_giantSignedGhostVisitBefore (Choices g) i p).trans ((choice g p).before i).symm
  · have hinj := giantSignedBirthLineage_injective (giantSignedChronologicalPreLineage h κ ha i g) hd
    have he' : (Sum.inr j : GiantSignedStateLiveSlots (h.state i) g) = Sum.inr l := hinj he
    exact Sum.inr.inj he'
  · exact (choice g ((h.state i).2.2.2 g j).1).before_particle i j rfl

include ha hd in
def giantSignedChronologicalAfterMemoryMatch (i : Fin (n+1)) (g : B) :
    GiantSignedLifespanMemory (giantSignedGhostVisitAfter (Choices g) i)
      (giantSignedLifespanResidue (Choices g) Offset i)
      (giantSignedMemoryGroupEquiv PB (giantSignedChronologicalGhostTarget h i) g) := by
  refine lifespanMemoryOfPrimeMembership _ _ _ (fun p => ?_) (fun j l he => ?_) (fun j => ?_)
  · exact (mem_giantSignedGhostVisitAfter (Choices g) i p).trans ((choice g p).after i).symm
  · let l₀ := giantSignedChronologicalVisitLineage h i g (giantSignedChronologicalPreLineage h κ ha i g)
    have hinj := giantSignedBirthLineage_injective l₀ hd
    have he' : (Sum.inr j : GiantSignedStateLiveSlots (giantSignedChronologicalAfterVisitState h i) g) =
      Sum.inr l := hinj he
    exact Sum.inr.inj he'
  · exact (choice g ((giantSignedChronologicalGhostTarget h i).2 g j).1).after_particle i j rfl

include hd in
theorem giantSignedChronologicalGhostMatch_of_prime (i : Fin (n+1)) (g : B) :
    GiantSignedChronologicalLifespanGhostMatch Choices h i g := by
  classical
  let born := giantSignedGhostVisitBorn (Choices g) i
  let m := giantSignedMemoryGroupEquiv PB (h.state i).2.2 g
  let f (j : Fin (batch i g)) : ↥born :=
    ⟨h.born i g j,(mem_giantSignedGhostVisitBorn (Choices g) i _).mpr
      (((choice g (h.born i g j)).born i).mp ⟨j,rfl⟩)⟩
  have hInj : Function.Injective f := by
    intro j l he
    apply (giantSignedChronologicalVisitBirth h i g).injective
    exact hd (congrArg (fun p : ↥born => p.val.val) he)
  have hSurj : Function.Surjective f := by
    intro p
    obtain ⟨j,hj⟩ := ((choice g p.val).born i).mpr
      ((mem_giantSignedGhostVisitBorn (Choices g) i p.val).mp p.property)
    exact ⟨j,Subtype.ext hj⟩
  let e := Equiv.ofBijective f ⟨hInj,hSurj⟩
  have hbatch : batch i g = born.card := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_congr e
  let order := (finCongr hbatch.symm).trans e
  refine ⟨order,?_⟩
  have hdel : h.deleted i g = giantSignedGhostVisitDeleted (Choices g) i m := by
    ext j
    exact ((choice g (m.2 j).1).deleted i j rfl).trans
      (mem_giantSignedGhostVisitDeleted (Choices g) i m (show Fin m.1 from j)).symm
  change (⟨h.deleted i g, batch i g, h.born i g⟩ : GiantSignedGhostMoves m) =
    ⟨giantSignedGhostVisitDeleted (Choices g) i m,born.card,giantSignedGhostVisitBornLabels order⟩
  apply Sigma.ext hdel
  apply heq_of_eq
  apply Sigma.ext hbatch
  exact tuple_heq_of_cast hbatch _ _ (fun _ => rfl)

end
end ArtinMatthews
