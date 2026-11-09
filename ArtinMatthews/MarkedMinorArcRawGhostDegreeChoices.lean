module

public import ArtinMatthews.MarkedMemoryHistoryGhostSum
public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedSubset


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite degree coordinates for the source and target total memory
cutoffs. Deletion coordinates remain literal subsets of old indices. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

@[ext] structure MarkedRawGhostDegrees (J : Type*) [Fintype J] (B : ℕ) where
  survivors : J → ℕ
  deleted : J → ℕ
  born : J → ℕ
  source_le : ∑ j, (survivors j+deleted j) ≤ B
  target_le : ∑ j, (survivors j+born j) ≤ B

theorem markedRawGhostDegrees_source_le {J : Type*} [Fintype J] {B : ℕ}
    (t : MarkedRawGhostDegrees J B) (j : J) : t.survivors j+t.deleted j ≤ B :=
  (Finset.single_le_sum (fun i _ => Nat.zero_le (t.survivors i+t.deleted i)) (Finset.mem_univ j)).trans t.source_le

theorem markedRawGhostDegrees_target_le {J : Type*} [Fintype J] {B : ℕ}
    (t : MarkedRawGhostDegrees J B) (j : J) : t.survivors j+t.born j ≤ B :=
  (Finset.single_le_sum (fun i _ => Nat.zero_le (t.survivors i+t.born i)) (Finset.mem_univ j)).trans t.target_le

def markedRawGhostDegreesEmbedding {J : Type*} [Fintype J] {B : ℕ} :
    MarkedRawGhostDegrees J B ↪ ((J → Fin (B+1)) × (J → Fin (B+1)) × (J → Fin (B+1))) where
  toFun t := (fun j => ⟨t.survivors j,by have := markedRawGhostDegrees_source_le t j; omega⟩,
    (fun j => ⟨t.deleted j,by have := markedRawGhostDegrees_source_le t j; omega⟩),
    (fun j => ⟨t.born j,by have := markedRawGhostDegrees_target_le t j; omega⟩))
  inj' := by
    intro a b h
    apply MarkedRawGhostDegrees.ext
    · funext j
      exact congrArg (fun v => (v.1 j:ℕ)) h
    · funext j
      exact congrArg (fun v => (v.2.1 j:ℕ)) h
    · funext j
      exact congrArg (fun v => (v.2.2 j:ℕ)) h

instance {J : Type*} [Fintype J] {B : ℕ} : Finite (MarkedRawGhostDegrees J B) :=
  Finite.of_injective markedRawGhostDegreesEmbedding markedRawGhostDegreesEmbedding.injective

instance {J : Type*} [Fintype J] {B : ℕ} : Fintype (MarkedRawGhostDegrees J B) := Fintype.ofFinite _

def markedRawGhostDegreesSourceSizes {J : Type*} [Fintype J] {B : ℕ}
    (t : MarkedRawGhostDegrees J B) : MarkedRawMemorySizes J B :=
  ⟨fun j => ⟨t.survivors j+t.deleted j,by have := markedRawGhostDegrees_source_le t j; omega⟩,t.source_le⟩

abbrev MarkedRawGhostShape (J : Type*) [Fintype J] (B : ℕ) :=
  Σ k : MarkedRawMemorySizes J B, Σ del : (j : J) → Finset (Fin (k.1 j:ℕ)),
    {l : J → Fin (B+1) // ∑ j, ((Finset.univ \ del j).card+(l j:ℕ)) ≤ B}

abbrev MarkedRawGhostDegreeShape (J : Type*) [Fintype J] (B : ℕ) :=
  Σ t : MarkedRawGhostDegrees J B,
    (j : J) → MarkedRawDeletionBatch (t.survivors j+t.deleted j) (t.deleted j)

def markedRawGhostDegreeShapeToShape {J : Type*} [Fintype J] {B : ℕ}
    (a : MarkedRawGhostDegreeShape J B) : MarkedRawGhostShape J B :=
  ⟨markedRawGhostDegreesSourceSizes a.1,fun j => (a.2 j).1,
    ⟨fun j => ⟨a.1.born j,by have := markedRawGhostDegrees_target_le a.1 j; omega⟩,by
      have hn (j : J) : (Finset.univ \ (a.2 j).1).card=a.1.survivors j :=
        by simpa only [Finset.compl_eq_univ_sdiff] using
          markedRawDeletionBatch_survivor_card rfl (a.2 j)
      exact (Finset.sum_le_sum (fun j _ => Nat.add_le_add_right (hn j).le _)).trans a.1.target_le⟩⟩

theorem markedRawGhostDegreeShapeToShape_injective {J : Type*} [Fintype J] {B : ℕ} :
    Function.Injective (markedRawGhostDegreeShapeToShape (J := J) (B := B)) := by
  intro a b hab
  have ht : a.1=b.1 := by
    apply MarkedRawGhostDegrees.ext
    · funext j
      have hh := congrArg (fun v : MarkedRawGhostShape J B => (Finset.univ \ v.2.1 j).card) hab
      change (Finset.univ \ (a.2 j).1).card=(Finset.univ \ (b.2 j).1).card at hh
      have ha := markedRawDeletionBatch_survivor_card rfl (a.2 j)
      have hb := markedRawDeletionBatch_survivor_card rfl (b.2 j)
      rw [Finset.compl_eq_univ_sdiff] at ha hb
      exact ha.symm.trans (hh.trans hb)
    · funext j
      have hh := congrArg (fun v : MarkedRawGhostShape J B => (v.2.1 j).card) hab
      change (a.2 j).1.card=(b.2 j).1.card at hh
      exact (markedRawDeletionBatch_deleted_card (a.2 j)).symm.trans
        (hh.trans (markedRawDeletionBatch_deleted_card (b.2 j)))
    · exact congrArg (fun v : MarkedRawGhostShape J B => fun j => (v.2.2.1 j:ℕ)) hab
  rcases a with ⟨t,S⟩
  rcases b with ⟨t',S'⟩
  dsimp only at ht
  cases ht
  have htail := eq_of_heq (Sigma.mk.inj_iff.mp hab).2
  have hdel := congrArg Sigma.fst htail
  have hS : S=S' := by
    funext j
    apply Subtype.ext
    exact congrFun hdel j
  cases hS
  rfl

theorem markedRawGhostDegreeShapeToShape_surjective {J : Type*} [Fintype J] {B : ℕ} :
    Function.Surjective (markedRawGhostDegreeShapeToShape (J := J) (B := B)) := by
  rintro ⟨k,del,l⟩
  let t : MarkedRawGhostDegrees J B :=
    ⟨fun j => (Finset.univ \ del j).card,fun j => (del j).card,fun j => (l.1 j:ℕ),by
      have hh (j : J) : (Finset.univ \ del j).card+(del j).card=(k.1 j:ℕ) := by
        simpa only [Finset.card_univ,Fintype.card_fin] using
          Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (del j))
      simpa only [hh] using k.2,l.2⟩
  have hn (j : J) : (Finset.univ \ del j).card=t.survivors j := rfl
  have hd (j : J) : (del j).card=t.deleted j := rfl
  have hl (j : J) : (l.1 j:ℕ)=t.born j := rfl
  clear_value t
  have hk : markedRawGhostDegreesSourceSizes t=k := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (del j))
    simpa only [markedRawGhostDegreesSourceSizes,Finset.card_univ,Fintype.card_fin,hn,hd] using hh
  cases hk
  let S : (j : J) → MarkedRawDeletionBatch (t.survivors j+t.deleted j) (t.deleted j) :=
    fun j => ⟨del j,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hd j⟩⟩
  refine ⟨⟨t,S⟩,?_⟩
  dsimp only [markedRawGhostDegreeShapeToShape,S]
  apply congrArg (fun tail => (⟨markedRawGhostDegreesSourceSizes t,tail⟩ : MarkedRawGhostShape J B))
  apply congrArg (fun tail => (⟨del,tail⟩ : Σ d : (j : J) → Finset (Fin ((markedRawGhostDegreesSourceSizes t).1 j:ℕ)),
    {l : J → Fin (B+1) // ∑ j, ((Finset.univ \ d j).card+(l j:ℕ)) ≤ B}))
  apply Subtype.ext
  funext j
  apply Fin.ext
  exact (hl j).symm

def markedRawGhostDegreeShapeEquiv {J : Type*} [Fintype J] {B : ℕ} :
    MarkedRawGhostDegreeShape J B ≃ MarkedRawGhostShape J B :=
  Equiv.ofBijective markedRawGhostDegreeShapeToShape
    ⟨markedRawGhostDegreeShapeToShape_injective,markedRawGhostDegreeShapeToShape_surjective⟩

end
end ArtinMatthews
