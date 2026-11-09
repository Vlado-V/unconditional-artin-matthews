module

public import ArtinMatthews.GiantSignedSmallTransferEvents


set_option backward.privateInPublic true
@[expose] public section

/-! The exceptional omission set is the union over actual old pending
indices. Its cardinality is bounded by the full memory length. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

section Memory
variable {S : Type*} [Fintype S] [DecidableEq S] {P : S → Finset ℕ} {M ell : ℕ}

def giantSignedSmallParticleOmissions {Q : Finset ℕ}
    (a : MarkedPhysicalMarking P M) (z : ℤ) (DBig : ℕ) (x : GiantSignedParticle Q) :
    Finset (GiantSignedSmallOmission S M ell) :=
  Finset.univ.filter fun U => GiantSignedSmallTransferEvent a x.2
    (z : ZMod x.1.val) DBig U

theorem giantSignedSmallParticleOmissions_card_le_one {Q : Finset ℕ}
    (hP : ∀ g q, q ∈ P g → q.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hsep : ∀ g, Disjoint (P g) Q)
    (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a)
    (z : ℤ) (DBig : ℕ) (x : GiantSignedParticle Q)
    (hz : (z : ZMod x.1.val) ≠ 0)
    (hbound : ∀ U : GiantSignedSmallOmission S M ell, giantSignedSmallOmittedProduct a U < x.1.val) :
    (giantSignedSmallParticleOmissions (ell := ell) a z DBig x).card ≤ 1 := by
  let : Fact x.1.val.Prime := ⟨hQ x.1.val x.1.property⟩
  apply Finset.card_le_one.mpr
  intro U hU V hV
  exact giantSignedSmallTransfer_unique hP hdis a ha x.2 (z : ZMod x.1.val) hz DBig
    (giantSignedSmallFull_ne_zero_mod hP a Q x.1.property hsep) hbound U V
    (Finset.mem_filter.mp hU).2 (Finset.mem_filter.mp hV).2

def GiantSignedSmallMemoryAllows {J : Type*} {Q : J → Finset ℕ}
    (a : MarkedPhysicalMarking P M) (z : ℤ) (DBig : ℕ) (m : GiantSignedMemory Q)
    (U : GiantSignedSmallOmission S M ell) : Prop :=
  ∃ j i, GiantSignedSmallTransferEvent a (m.2 j i).2
    (z : ZMod (m.2 j i).1.val) DBig U

def giantSignedSmallMemoryOmissions {J : Type*} {Q : J → Finset ℕ}
    (a : MarkedPhysicalMarking P M) (z : ℤ) (DBig : ℕ) (m : GiantSignedMemory Q) :
    Finset (GiantSignedSmallOmission S M ell) :=
  Finset.univ.filter (GiantSignedSmallMemoryAllows a z DBig m)

theorem giantSignedSmallMemoryOmissions_card_le {J : Type*} [Fintype J]
    (Q : J → Finset ℕ)
    (hP : ∀ g q, q ∈ P g → q.Prime) (hQ : ∀ j q, q ∈ Q j → q.Prime)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hsep : ∀ g j, Disjoint (P g) (Q j))
    (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a)
    (z : ℤ) (DBig : ℕ) (m : GiantSignedMemory Q)
    (hz : ∀ j i, (z : ZMod (m.2 j i).1.val) ≠ 0)
    (hbound : ∀ j i (U : GiantSignedSmallOmission S M ell),
      giantSignedSmallOmittedProduct a U < (m.2 j i).1.val) :
    (giantSignedSmallMemoryOmissions (ell := ell) a z DBig m).card ≤ ∑ j, m.1 j := by
  classical
  let E (i : Σ j, Fin (m.1 j)) := giantSignedSmallParticleOmissions (ell := ell) a z DBig (m.2 i.1 i.2)
  have he : giantSignedSmallMemoryOmissions (ell := ell) a z DBig m = Finset.univ.biUnion E := by
    ext U
    simp only [giantSignedSmallMemoryOmissions, Finset.mem_filter, Finset.mem_univ,
      true_and, GiantSignedSmallMemoryAllows, Finset.mem_biUnion]
    constructor
    · rintro ⟨j, i, hi⟩
      refine ⟨⟨j, i⟩, ?_⟩
      change U ∈ giantSignedSmallParticleOmissions (ell := ell) a z DBig (m.2 j i)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    · rintro ⟨⟨j, i⟩, hi⟩
      change U ∈ giantSignedSmallParticleOmissions (ell := ell) a z DBig (m.2 j i) at hi
      exact ⟨j, i, (Finset.mem_filter.mp hi).2⟩
  rw [he]
  calc
    _ ≤ ∑ i : Σ j, Fin (m.1 j), (E i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Σ j, Fin (m.1 j), 1 := by
      apply Finset.sum_le_sum
      intro i _
      exact giantSignedSmallParticleOmissions_card_le_one hP (hQ i.1) hdis
        (fun g => hsep g i.1) a ha z DBig (m.2 i.1 i.2) (hz i.1 i.2) (hbound i.1 i.2)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Fintype.card_sigma, Fintype.card_fin, Nat.cast_id]

end Memory
end
end ArtinMatthews
