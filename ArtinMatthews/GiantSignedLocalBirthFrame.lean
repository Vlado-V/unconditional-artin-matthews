module

public import ArtinMatthews.GiantSignedCanonicalSlots
public import ArtinMatthews.GiantSignedUniformBirthRank


set_option backward.privateInPublic true
@[expose] public section

/-! Performed flags on the common frame are read from the original local
target slots and the actual ordered ghost batch. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {B : Type*} [Fintype B] {PB : B → Finset ℕ} {k ell n H : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

def giantSignedEdgeFrameValue {C : B → Finset (Fin k)}
    (target : MarkedPhysicalMarking PB (k+ell))
    (promoted : (g : B) → Finset (Fin (ell+(C g).card))) (g : B) (s : Fin (k+ell)) : Option ℕ :=
  Sum.elim (fun _ => none)
    (fun j => if j ∈ promoted g then none else some (giantSignedPatternFreeLabels C target g j).val)
    (giantSignedCanonicalSlotEquiv (C g) ell s)

def giantSignedVisitFrameValue (b : B → ℕ) (born : (g : B) → Fin (b g) → PB g)
    (g : B) (s : Fin H) : Option ℕ :=
  if hs : s.val < b g then some (born g ⟨s.val,hs⟩).val else none

theorem giantSignedUniformBirthEmbedding_edge_iff (d : GiantSignedBirthData PB ell C batch)
    (hH : ∀ i g, batch i g ≤ H) (i : Fin n) (g : B) (s : Fin (k+ell)) :
    (∃ a, giantSignedUniformBirthEmbedding d H hH a = .inr (.inl ⟨i,g,s⟩)) ↔
      ∃ j : Fin (ell+(C i g).card), j ∉ d.promoted i g ∧ giantSignedFreeSlotEmbedding (C i g) ell j = s := by
  constructor
  · rintro ⟨a,ha⟩
    rcases a with a | a
    · change (Sum.inl a : GiantSignedUniformBirthAddress B (k+ell) n H) =
        .inr (.inl ⟨i,g,s⟩) at ha
      cases ha
    · rcases a with ⟨j,h,t⟩ | a
      · have he : (⟨j,h,giantSignedFreeSlotEmbedding (C j h) ell t.val⟩ :
            Σ _ : Fin n, Σ _ : B, Fin (k+ell)) = ⟨i,g,s⟩ :=
          Sum.inl.inj (Sum.inr.inj ha)
        have hi : j = i := congrArg Sigma.fst he
        have hg : h = g := congrArg (fun z : Σ _ : Fin n, Σ _ : B, Fin (k+ell) => z.2.1) he
        subst i
        subst g
        exact ⟨t.val,t.property,
          congrArg (fun z : Σ _ : Fin n, Σ _ : B, Fin (k+ell) => z.2.2) he⟩
      · rcases a with ⟨j,g',u⟩
        change (Sum.inr (.inr ⟨j,g',⟨u.val,u.isLt.trans_le (hH j g')⟩⟩) :
          GiantSignedUniformBirthAddress B (k+ell) n H) = .inr (.inl ⟨i,g,s⟩) at ha
        have hn := Sum.inr.inj ha
        cases hn
  · rintro ⟨j,hj,he⟩
    exact ⟨.inr (.inl ⟨i,g,j,hj⟩), congrArg
      (fun u => (Sum.inr (.inl ⟨i,g,u⟩) : GiantSignedUniformBirthAddress B (k+ell) n H)) he⟩

theorem giantSignedUniformBirthValue_edge_frame (d : GiantSignedBirthData PB ell C batch)
    (hH : ∀ i g, batch i g ≤ H) (i : Fin n) (g : B) (s : Fin (k+ell)) :
    giantSignedUniformBirthValue d H hH (.inr (.inl ⟨i,g,s⟩)) =
      giantSignedEdgeFrameValue (d.target i) (d.promoted i) g s := by
  let e := giantSignedCanonicalSlotEquiv (C i g) ell
  obtain ⟨j,rfl⟩ := e.symm.surjective s
  rcases j with j | j
  · rw [show e.symm (.inl j) = Fin.castAdd ell j.val from giantSignedCanonicalSlotEquiv_symm_copied _ _ _]
    simp only [giantSignedEdgeFrameValue, giantSignedCanonicalSlotEquiv_copied, Sum.elim_inl]
    apply giantSignedUniformBirthValue_unperformed
    intro he
    obtain ⟨u,_,hu⟩ := (giantSignedUniformBirthEmbedding_edge_iff d hH i g _).mp he
    have h := congrArg e hu
    change giantSignedCanonicalSlotEquiv (C i g) ell (giantSignedFreeSlotEmbedding (C i g) ell u) =
      giantSignedCanonicalSlotEquiv (C i g) ell (Fin.castAdd ell j.val) at h
    rw [giantSignedCanonicalSlotEquiv_free, giantSignedCanonicalSlotEquiv_copied] at h
    cases h
  · rw [show e.symm (.inr j) = giantSignedFreeSlotEmbedding (C i g) ell j from
      giantSignedCanonicalSlotEquiv_symm_free _ _ _]
    simp only [giantSignedEdgeFrameValue, giantSignedCanonicalSlotEquiv_free, Sum.elim_inr]
    by_cases hj : j ∈ d.promoted i g
    · rw [ite_eq_left hj]
      apply giantSignedUniformBirthValue_unperformed
      intro he
      obtain ⟨u,hu,he⟩ := (giantSignedUniformBirthEmbedding_edge_iff d hH i g _).mp he
      have h := (giantSignedFreeSlotEmbedding (C i g) ell).injective he
      exact hu (h.symm ▸ hj)
    · rw [ite_eq_right hj]
      exact giantSignedUniformBirthValue_fresh d H hH i g j hj

theorem giantSignedUniformBirthValue_visit_frame (d : GiantSignedBirthData PB ell C batch)
    (hH : ∀ i g, batch i g ≤ H) (i : Fin (n+1)) (g : B) (s : Fin H) :
    giantSignedUniformBirthValue d H hH (.inr (.inr ⟨i,g,s⟩)) =
      giantSignedVisitFrameValue (batch i) (d.born i) g s := by
  by_cases hs : s.val < batch i g
  · let t : Fin (batch i g) := ⟨s.val,hs⟩
    have he : (⟨t.val,t.isLt.trans_le (hH i g)⟩ : Fin H) = s := Fin.ext rfl
    calc
      _ = some (d.born i g t).val := by
        rw [← he]
        exact giantSignedUniformBirthValue_ghost d H hH i g t
      _ = _ := by
        unfold giantSignedVisitFrameValue
        rw [dite_eq_left hs]
  · unfold giantSignedVisitFrameValue
    rw [dite_eq_right hs]
    apply giantSignedUniformBirthValue_unperformed
    rintro ⟨a,ha⟩
    rcases a with a | a
    · change (Sum.inl a : GiantSignedUniformBirthAddress B (k+ell) n H) =
        .inr (.inr ⟨i,g,s⟩) at ha
      cases ha
    · rcases a with a | ⟨j,h,t⟩
      · rcases a with ⟨j,g',u⟩
        change (Sum.inr (.inl ⟨j,g',giantSignedFreeSlotEmbedding (C j g') ell u.val⟩) :
          GiantSignedUniformBirthAddress B (k+ell) n H) = .inr (.inr ⟨i,g,s⟩) at ha
        have hn := Sum.inr.inj ha
        cases hn
      · have he : (⟨j,h,⟨t.val,t.isLt.trans_le (hH j h)⟩⟩ :
            Σ _ : Fin (n+1), Σ _ : B, Fin H) = ⟨i,g,s⟩ :=
          Sum.inr.inj (Sum.inr.inj ha)
        have hi : j = i := congrArg Sigma.fst he
        have hg : h = g := congrArg (fun z : Σ _ : Fin (n+1), Σ _ : B, Fin H => z.2.1) he
        subst i
        subst g
        have hv : t.val = s.val := congrArg
          (fun z : Σ _ : Fin (n+1), Σ _ : B, Fin H => z.2.2.val) he
        exact hs (hv ▸ t.isLt)

end
end ArtinMatthews
