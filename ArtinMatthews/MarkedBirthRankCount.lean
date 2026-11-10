module

public import ArtinMatthews.MarkedBirthDistinctPermutation


set_option backward.privateInPublic true
@[expose] public section

/-! A rank-r permutation moves at most 2r addresses. Encoding its moved
input/output pairs gives an explicit finite coefficient-mass bound. The
bound is slightly larger than a minimal-transposition count and still has
the required polynomial-in-address-count base to the power O(r). -/

noncomputable section
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

def markedBirthRankEncoding {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A]
    (r : ℕ) (σ : {σ : Equiv.Perm A // markedBirthPermutationRank σ = r})
    (k : Fin (2*r)) : Option (A × A) :=
  if hk : k.1 < σ.1.support.card then
    let a := σ.1.support.orderEmbOfFin rfl ⟨k.1,hk⟩
    some (a,σ.1 a)
  else none

theorem markedBirthRankEncoding_value
    {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A]
    (r : ℕ) (σ : {σ : Equiv.Perm A // markedBirthPermutationRank σ = r})
    (k : Fin (2*r)) (a b : A) (h : markedBirthRankEncoding r σ k = some (a,b)) : σ.1 a = b := by
  unfold markedBirthRankEncoding at h
  split_ifs at h with hk
  · have hp := Option.some.inj h
    have ha := congrArg Prod.fst hp
    have hb := congrArg Prod.snd hp
    exact (congrArg σ.1 ha).symm.trans hb

theorem markedBirthRankEncoding_covers
    {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A]
    (r : ℕ) (σ : {σ : Equiv.Perm A // markedBirthPermutationRank σ = r})
    (a : A) (ha : a ∈ σ.1.support) :
    ∃ k : Fin (2*r), markedBirthRankEncoding r σ k = some (a,σ.1 a) := by
  let i := (σ.1.support.orderIsoOfFin rfl).symm ⟨a,ha⟩
  have hc := markedBirthPermutation_support_le_twice_rank σ.1
  rw [σ.2] at hc
  let k : Fin (2*r) := ⟨i.1,i.2.trans_le hc⟩
  have hi : σ.1.support.orderEmbOfFin rfl i = a :=
    congrArg Subtype.val ((σ.1.support.orderIsoOfFin rfl).apply_symm_apply ⟨a,ha⟩)
  refine ⟨k,?_⟩
  unfold markedBirthRankEncoding
  rw [dite_eq_left i.2]
  change some (σ.1.support.orderEmbOfFin rfl i,σ.1 (σ.1.support.orderEmbOfFin rfl i)) = _
  rw [hi]

theorem markedBirthRankEncoding_injective
    {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A] (r : ℕ) :
    Function.Injective (markedBirthRankEncoding (A := A) r) := by
  intro σ τ h
  apply Subtype.ext
  apply Equiv.ext
  intro a
  by_cases hs : a ∈ σ.1.support
  · obtain ⟨k,hk⟩ := markedBirthRankEncoding_covers r σ a hs
    have ht := (congrFun h k).symm.trans hk
    exact (markedBirthRankEncoding_value r τ k a (σ.1 a) ht).symm
  · by_cases ht : a ∈ τ.1.support
    · obtain ⟨k,hk⟩ := markedBirthRankEncoding_covers r τ a ht
      exact markedBirthRankEncoding_value r σ k a (τ.1 a) ((congrFun h k).trans hk)
    · have hσ : σ.1 a = a := by
        by_contra hn
        exact hs (Equiv.Perm.mem_support.mpr hn)
      have hτ : τ.1 a = a := by
        by_contra hn
        exact ht (Equiv.Perm.mem_support.mpr hn)
      exact hσ.trans hτ.symm

theorem markedBirthPermutation_rank_card_bound_ordered
    {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A] (r : ℕ) :
    Fintype.card {σ : Equiv.Perm A // markedBirthPermutationRank σ = r} ≤
      (Fintype.card A*Fintype.card A+1)^(2*r) := by
  have h := Fintype.card_le_of_injective _ (markedBirthRankEncoding_injective (A := A) r)
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_option, Fintype.card_prod] using h

theorem markedBirthPermutation_rank_card_bound
    {A : Type*} [Fintype A] [DecidableEq A] (r : ℕ) :
    Fintype.card {σ : Equiv.Perm A // markedBirthPermutationRank σ = r} ≤
      (Fintype.card A*Fintype.card A+1)^(2*r) := by
  let _ : LinearOrder A := LinearOrder.lift' (Fintype.equivFin A) (Fintype.equivFin A).injective
  exact markedBirthPermutation_rank_card_bound_ordered r

end ArtinMatthews
