module

public import ArtinMatthews.GiantSignedBirthChronology
public import ArtinMatthews.MarkedBirthChronologicalPivots


set_option backward.privateInPublic true
@[expose] public section

/-! Every nontrivial cycle of the actual uniform frame has an earliest
performed pivot. Its dependent addresses split exactly over the local draws. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {B : Type*} [Fintype B] {M n H : ℕ}

def giantSignedUniformBirthNonpivots
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) :
    Finset (GiantSignedUniformBirthAddress B M n H) :=
  @markedBirthCycleNonpivots (GiantSignedUniformBirthAddress B M n H) inferInstance inferInstance
    giantSignedUniformBirthChronologicalOrder σ

def giantSignedUniformBirthPivot
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) :
    GiantSignedUniformBirthAddress B M n H → GiantSignedUniformBirthAddress B M n H :=
  @markedBirthChronologicalPivot (GiantSignedUniformBirthAddress B M n H) inferInstance inferInstance
    giantSignedUniformBirthChronologicalOrder σ

theorem giantSignedUniformBirthNonpivots_card
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) :
    (giantSignedUniformBirthNonpivots σ).card = markedBirthPermutationRank σ :=
  @markedBirthCycleNonpivots_card (GiantSignedUniformBirthAddress B M n H) inferInstance inferInstance
    giantSignedUniformBirthChronologicalOrder σ

theorem giantSignedUniformBirthPivot_earlier
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n H))
    {a : GiantSignedUniformBirthAddress B M n H} (ha : a ∈ giantSignedUniformBirthNonpivots σ) :
    GiantSignedUniformBirthEarlier (giantSignedUniformBirthPivot σ a) a :=
  @markedBirthChronologicalPivot_lt (GiantSignedUniformBirthAddress B M n H) inferInstance inferInstance
    giantSignedUniformBirthChronologicalOrder σ a ha

theorem giantSignedUniformBirthPivot_event {P : Type*}
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n H))
    (p : GiantSignedUniformBirthAddress B M n H → Option P)
    (hσ : MarkedBirthPermutationEvent p σ)
    {a : GiantSignedUniformBirthAddress B M n H} (ha : a ∈ giantSignedUniformBirthNonpivots σ) :
    GiantSignedUniformBirthEarlier (giantSignedUniformBirthPivot σ a) a ∧
      giantSignedUniformBirthPivot σ a ∈ σ.support ∧ a ∈ σ.support ∧
      p a = p (giantSignedUniformBirthPivot σ a) ∧ p a ≠ none :=
  @markedBirthChronologicalPivot_event (GiantSignedUniformBirthAddress B M n H) P
    inferInstance inferInstance giantSignedUniformBirthChronologicalOrder σ p hσ a ha

theorem giantSignedUniformBirthEvent_iff_pivots {P : Type*}
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n H))
    (p : GiantSignedUniformBirthAddress B M n H → Option P) :
    MarkedBirthPermutationEvent p σ ↔
      (∀ a ∈ σ.support, p a ≠ none) ∧
      (∀ a ∈ giantSignedUniformBirthNonpivots σ, p a = p (giantSignedUniformBirthPivot σ a)) :=
  @markedBirthPermutationEvent_iff_pivots (GiantSignedUniformBirthAddress B M n H) P
    inferInstance inferInstance giantSignedUniformBirthChronologicalOrder σ p

def giantSignedUniformBirthStageNonpivots
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) (o : GiantSignedBirthOperation n) :
    Finset (GiantSignedUniformBirthAddress B M n H) :=
  (giantSignedUniformBirthNonpivots σ).filter (fun a => giantSignedUniformBirthOperation M n H a = o)

theorem giantSignedUniformBirthStageNonpivots_card_sum
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) :
    (∑ o : GiantSignedBirthOperation n, (giantSignedUniformBirthStageNonpivots σ o).card) =
      markedBirthPermutationRank σ := by
  rw [← giantSignedUniformBirthNonpivots_card σ]
  symm
  exact Finset.card_eq_sum_card_fiberwise (fun a _ =>
    Finset.mem_univ (giantSignedUniformBirthOperation M n H a))

theorem giantSignedUniformBirthStageNonpivots_atom_product
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) (Δ : ℝ) :
    (∏ o : GiantSignedBirthOperation n, Δ^(giantSignedUniformBirthStageNonpivots σ o).card) =
      Δ^(markedBirthPermutationRank σ) := by
  rw [Finset.prod_pow_eq_pow_sum, giantSignedUniformBirthStageNonpivots_card_sum]

theorem giantSignedUniformBirthActualEvent_iff_pivots
    {P : B → Finset ℕ} {k ell : ℕ} {C : Fin n → B → Finset (Fin k)}
    {batch : Fin (n+1) → B → ℕ} (d : GiantSignedBirthData P ell C batch)
    (hH : ∀ i g, batch i g ≤ H)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H)) :
    MarkedBirthPermutationEvent (giantSignedUniformBirthValue d H hH) σ ↔
      (∀ a ∈ σ.support, giantSignedUniformBirthValue d H hH a ≠ none) ∧
      (∀ a ∈ giantSignedUniformBirthNonpivots σ,
        giantSignedUniformBirthValue d H hH a =
          giantSignedUniformBirthValue d H hH (giantSignedUniformBirthPivot σ a)) :=
  giantSignedUniformBirthEvent_iff_pivots σ (giantSignedUniformBirthValue d H hH)

end
end ArtinMatthews
