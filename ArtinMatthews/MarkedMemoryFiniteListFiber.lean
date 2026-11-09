module

public import ArtinMatthews.MarkedMemoryFiniteLists
public import ArtinMatthews.MarkedMemoryHistoryBirthQuotient


set_option backward.privateInPublic true
@[expose] public section

/-! Forgetting the order of a finite injective identity list has the
literal factorial enumeration fiber. No distinctness of numeric marks
is used. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {A : Type*} [Fintype A] [DecidableEq A]

def markedMemoryFiniteListSet (l : MarkedMemoryFiniteList A) : Finset A :=
  markedMemoryBirthBatch ⟨l.1.2,l.2⟩

omit [DecidableEq A] in
theorem markedMemoryFiniteListSet_card (l : MarkedMemoryFiniteList A) :
    (markedMemoryFiniteListSet l).card = l.1.1.val := markedMemoryBirthBatch_card _

omit [DecidableEq A] in
theorem markedMemoryFiniteListSet_mem (l : MarkedMemoryFiniteList A) (a : A) :
    a ∈ markedMemoryFiniteListSet l ↔ a ∈ markedMemoryFiniteList_toList l := by
  simp only [markedMemoryFiniteListSet,markedMemoryBirthBatch,Finset.mem_map,Finset.mem_univ,
    true_and,markedMemoryFiniteList_toList,List.mem_ofFn]
  rfl

def markedMemoryFiniteListOfEmbedding {m : ℕ} (e : Fin m ↪ A) : MarkedMemoryFiniteList A :=
  ⟨⟨⟨m,Nat.lt_succ_of_le (by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective)⟩,e⟩,e.injective⟩

omit [DecidableEq A] in
theorem markedMemoryFiniteListOfEmbedding_set {m : ℕ} (e : Fin m ↪ A) :
    markedMemoryFiniteListSet (markedMemoryFiniteListOfEmbedding e) = markedMemoryBirthBatch e := rfl

omit [DecidableEq A] in
theorem markedMemoryFiniteListOfEmbedding_recover (l : MarkedMemoryFiniteList A) :
    markedMemoryFiniteListOfEmbedding (⟨l.1.2,l.2⟩ : Fin l.1.1.val ↪ A) = l := by
  rcases l with ⟨⟨⟨m,hm⟩,f⟩,hf⟩
  rfl

omit [Fintype A] [DecidableEq A] in
theorem markedMemoryBirthBatch_castDomain {m k : ℕ} (h : m = k) (e : Fin m ↪ A) :
    markedMemoryBirthBatch ((Equiv.cast (congrArg Fin h.symm)).toEmbedding.trans e) =
      markedMemoryBirthBatch e := by
  cases h
  rfl

omit [DecidableEq A] in
theorem markedMemoryFiniteListOfEmbedding_castDomain {m k : ℕ} (h : m = k) (e : Fin m ↪ A) :
    markedMemoryFiniteListOfEmbedding ((Equiv.cast (congrArg Fin h.symm)).toEmbedding.trans e) =
      markedMemoryFiniteListOfEmbedding e := by
  cases h
  rfl

def markedMemoryFiniteListFiberEmbedding (S : Finset A) :
    {l : MarkedMemoryFiniteList A // markedMemoryFiniteListSet l = S} ≃
      {e : Fin S.card ↪ A // markedMemoryBirthBatch e = S} where
  toFun l := by
    have hk : l.1.1.1.val = S.card := (markedMemoryFiniteListSet_card l.1).symm.trans (congrArg Finset.card l.2)
    exact ⟨(Equiv.cast (congrArg Fin hk.symm)).toEmbedding.trans ⟨l.1.1.2,l.1.2⟩,
      (markedMemoryBirthBatch_castDomain hk _).trans l.2⟩
  invFun e := ⟨markedMemoryFiniteListOfEmbedding e.1,e.2⟩
  left_inv l := by
    apply Subtype.ext
    have hk : l.1.1.1.val = S.card := (markedMemoryFiniteListSet_card l.1).symm.trans (congrArg Finset.card l.2)
    exact (markedMemoryFiniteListOfEmbedding_castDomain hk _).trans
      (markedMemoryFiniteListOfEmbedding_recover l.1)
  right_inv e := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl

def markedMemoryFiniteListFiberEquiv (S : Finset A) :
    {l : MarkedMemoryFiniteList A // markedMemoryFiniteListSet l = S} ≃ Equiv.Perm (Fin S.card) :=
  (markedMemoryFiniteListFiberEmbedding S).trans
    ((Equiv.subtypeEquivRight (fun e => by
      exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩)).trans
      ((markedMemoryBirthFiberEquiv (⟨S,rfl⟩ : MarkedMemoryBirthSets A S.card)).trans
        (Equiv.equivCongr (Equiv.refl _) (Finset.equivFin S))))

theorem markedMemoryFiniteListFiber_card (S : Finset A) :
    Fintype.card {l : MarkedMemoryFiniteList A // markedMemoryFiniteListSet l = S} = S.card.factorial := by
  rw [Fintype.card_congr (markedMemoryFiniteListFiberEquiv S),Fintype.card_perm,Fintype.card_fin]

def markedMemoryFiniteListCanonical (S : Finset A) : MarkedMemoryFiniteList A :=
  ((markedMemoryFiniteListFiberEquiv S).symm (Equiv.refl _)).1

omit [DecidableEq A] in
theorem markedMemoryFiniteListCanonical_set (S : Finset A) :
    markedMemoryFiniteListSet (markedMemoryFiniteListCanonical S) = S :=
  ((markedMemoryFiniteListFiberEquiv S).symm (Equiv.refl _)).2

end
end ArtinMatthews
