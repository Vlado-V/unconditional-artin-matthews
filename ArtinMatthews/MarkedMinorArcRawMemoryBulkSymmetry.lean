module

public import ArtinMatthews.MarkedMinorArcRawMemoryBulkIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! Actual symmetric-pending transport for an unordered batch of deleted
old indices, with the birth-compatible order survivors followed by births. -/
namespace ArtinMatthews
open scoped BigOperators

theorem markedRawSubsetIndexEquiv_deleted {k : ℕ} (S : Finset (Fin k)) (i : Fin S.card) :
    markedRawSubsetIndexEquiv S (Sum.inl i)=S.orderEmbOfFin rfl i := rfl

theorem markedRawSubsetIndexEquiv_survivor {k : ℕ} (S : Finset (Fin k)) (i : Fin (Sᶜ).card) :
    markedRawSubsetIndexEquiv S (Sum.inr i)=(Sᶜ).orderEmbOfFin rfl i := rfl

/-- Canonical old ordering puts the surviving block first and the deleted
block last, matching the actual ordered birth append operation. -/
def markedRawSubsetCanonicalIndex {k : ℕ} (S : Finset (Fin k)) :
    Fin S.card ⊕ Fin (Sᶜ).card ≃ Fin k :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by
    simpa only [Nat.add_comm] using markedRawSubsetIndex_card S)))

def markedRawSubsetCanonicalTuple {X : Type*} {k : ℕ} (S : Finset (Fin k))
    (deleted : Fin S.card → X) (survivors : Fin (Sᶜ).card → X) : Fin k → X :=
  (Sum.elim deleted survivors) ∘ (markedRawSubsetCanonicalIndex S).symm

/-- This actual index permutation compares old subset order with the
canonical survivor-then-deleted ordering; no particle values are quotiented. -/
def markedRawSubsetReassemblyPerm {k : ℕ} (S : Finset (Fin k)) : Equiv.Perm (Fin k) :=
  (markedRawSubsetIndexEquiv S).symm.trans (markedRawSubsetCanonicalIndex S)

/-- Reassembling the actual old tuple is exactly canonical append followed
by the explicit old-index permutation. -/
theorem markedRawSubsetTupleEquiv_inverse {X : Type*} {k : ℕ} (S : Finset (Fin k))
    (deleted : Fin S.card → X) (survivors : Fin (Sᶜ).card → X) :
    (markedRawSubsetTupleEquiv S).symm (deleted,survivors)=
      (markedRawSubsetCanonicalTuple S deleted survivors) ∘ markedRawSubsetReassemblyPerm S := by
  apply (markedRawSubsetTupleEquiv (X := X) S).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · funext i
    rw [markedRawSubsetTupleEquiv_deleted]
    rw [← markedRawSubsetIndexEquiv_deleted]
    simp only [Function.comp_apply,markedRawSubsetCanonicalTuple,markedRawSubsetReassemblyPerm,
      Equiv.trans_apply,Equiv.symm_apply_apply,Sum.elim_inl]
  · funext i
    rw [markedRawSubsetTupleEquiv_survivor]
    rw [← markedRawSubsetIndexEquiv_survivor]
    simp only [Function.comp_apply,markedRawSubsetCanonicalTuple,markedRawSubsetReassemblyPerm,
      Equiv.trans_apply,Equiv.symm_apply_apply,Sum.elim_inr]

/-- A genuinely symmetric source pending test is invariant under the actual
unordered-deletion coordinate transport. -/
theorem markedRawTupleSymmetric_subset {X : Type*} {k : ℕ} (S : Finset (Fin k))
    (g : (Fin k → X) → ℂ) (hg : MarkedRawTupleSymmetric k g)
    (deleted : Fin S.card → X) (survivors : Fin (Sᶜ).card → X) :
    g ((markedRawSubsetTupleEquiv S).symm (deleted,survivors))=
      g (markedRawSubsetCanonicalTuple S deleted survivors) := by
  rw [markedRawSubsetTupleEquiv_inverse]
  exact hg _ _

/-- Genuine finite symmetric-Fock subset integration, with the actual old
index partition and canonical birth-compatible ordering made explicit. -/
theorem markedRawMemory_subset_symmetric_integral {X : Type*} [Fintype X] {k : ℕ}
    (S : Finset (Fin k)) (μ : X → ℂ)
    (g : (Fin k → X) → ℂ) (hg : MarkedRawTupleSymmetric k g)
    (f : (Fin S.card → X) → (Fin (Sᶜ).card → X) → ℂ) :
    (∑ a : Fin k → X, (∏ i, μ (a i))*g a*
      f (markedRawSubsetTupleEquiv S a).1 (markedRawSubsetTupleEquiv S a).2)=
      ∑ deleted : Fin S.card → X, ∑ survivors : Fin (Sᶜ).card → X,
        (∏ i, μ (deleted i))*(∏ i, μ (survivors i))*
          g (markedRawSubsetCanonicalTuple S deleted survivors)*f deleted survivors := by
  classical
  rw [← Equiv.sum_comp (markedRawSubsetTupleEquiv (X := X) S).symm]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro deleted _
  apply Finset.sum_congr rfl
  intro survivors _
  have he := (markedRawSubsetTupleEquiv (X := X) S).apply_symm_apply (deleted,survivors)
  rw [markedRawSubsetTupleEquiv_mass S μ,he,markedRawTupleSymmetric_subset S g hg]

end ArtinMatthews
