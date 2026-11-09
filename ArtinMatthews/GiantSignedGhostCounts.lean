module

public import ArtinMatthews.GiantSignedGhostRow


set_option backward.privateInPublic true
@[expose] public section

/-! Actual zero-residue counts split over the selected old indices and
their ordered survivors. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def giantSignedGroupZeroCount {P : Finset ℕ} {n : ℕ}
    (a : Fin n → GiantSignedParticle P) : ℕ := (giantSignedGhostZeroIndices ⟨n, a⟩).card

theorem giantSignedGroupZeroCount_sum {P : Finset ℕ} {n : ℕ}
    (a : Fin n → GiantSignedParticle P) :
    giantSignedGroupZeroCount a = ∑ i, if (a i).2 = 0 then 1 else 0 := by
  classical
  exact Finset.card_filter _ _

theorem giantSignedGroupZeroCount_partition {P : Finset ℕ} {n : ℕ}
    (a : Fin n → GiantSignedParticle P) (S : Finset (Fin n)) :
    giantSignedGroupZeroCount a =
      giantSignedGroupZeroCount (markedRawSubsetTupleEquiv S a).1 +
        giantSignedGroupZeroCount (markedRawSubsetTupleEquiv S a).2 := by
  classical
  have h := (markedRawSubsetIndexEquiv S).sum_comp
    (fun i : Fin n => if (a i).2 = 0 then (1 : ℕ) else 0)
  rw [Fintype.sum_sum_type] at h
  rw [giantSignedGroupZeroCount_sum, giantSignedGroupZeroCount_sum, giantSignedGroupZeroCount_sum]
  exact h.symm

theorem giantSignedGhost_deleted_zero_iff {P : Finset ℕ} {n : ℕ}
    (a : Fin n → GiantSignedParticle P) (S : Finset (Fin n)) :
    (∀ i, ((markedRawSubsetTupleEquiv S a).1 i).2 = 0) ↔
      S ⊆ giantSignedGhostZeroIndices ⟨n, a⟩ := by
  classical
  constructor
  · intro h i hi
    have hx := h ((S.orderIsoOfFin rfl).symm ⟨i, hi⟩)
    rw [markedRawSubsetTupleEquiv_deleted] at hx
    change (a ((S.orderIsoOfFin rfl ((S.orderIsoOfFin rfl).symm ⟨i, hi⟩)).val)).2 = 0 at hx
    have he := congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩)
    rw [he] at hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  · intro h i
    rw [markedRawSubsetTupleEquiv_deleted]
    have hi : S.orderEmbOfFin rfl i ∈ S := (S.orderIsoOfFin rfl i).property
    exact (Finset.mem_filter.mp (h hi)).2

theorem giantSignedGhost_survivor_zero_count {P : Finset ℕ} {n : ℕ}
    (a : Fin n → GiantSignedParticle P) (S : Finset (Fin n))
    (hS : S ⊆ giantSignedGhostZeroIndices ⟨n, a⟩) :
    giantSignedGroupZeroCount (markedRawSubsetTupleEquiv S a).2 =
      giantSignedGroupZeroCount a - S.card := by
  classical
  have hz := (giantSignedGhost_deleted_zero_iff a S).mpr hS
  have hd : giantSignedGroupZeroCount (markedRawSubsetTupleEquiv S a).1 = S.card := by
    simp [giantSignedGroupZeroCount_sum, hz]
  have hp := giantSignedGroupZeroCount_partition a S
  omega

end
end ArtinMatthews
