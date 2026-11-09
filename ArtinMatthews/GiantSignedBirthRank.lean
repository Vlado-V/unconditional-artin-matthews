module

public import ArtinMatthews.GiantSignedBirthAddresses
public import ArtinMatthews.MarkedBirthRankCount
public import Mathlib.Data.Fintype.Perm


set_option backward.privateInPublic true
@[expose] public section

/-! Exact signed rank expansion on the performed births of the original
row choices. Batch lengths are arbitrary natural numbers. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {B : Type*} [Fintype B] [DecidableEq B] {P : B → Finset ℕ}
    {k ell n : ℕ} {C : Fin n → B → Finset (Fin k)}
    {batch : Fin (n+1) → B → ℕ}

local instance giantSignedBirthPermutationFintype :
    Fintype (Equiv.Perm (GiantSignedBirthAddress B ell C batch)) :=
  @Equiv.instFintype (GiantSignedBirthAddress B ell C batch)
    (GiantSignedBirthAddress B ell C batch) inferInstance inferInstance inferInstance inferInstance

def GiantSignedBirthPermutationEvent (d : GiantSignedBirthData P ell C batch)
    (σ : Equiv.Perm (GiantSignedBirthAddress B ell C batch)) : Prop :=
  MarkedBirthPermutationEvent (giantSignedBirthValue d) σ

theorem giantSignedBirthDistinct_permutation_sum (d : GiantSignedBirthData P ell C batch) :
    (if GiantSignedBirthDistinct d then (1 : ℤ) else 0) =
      ∑ σ : Equiv.Perm (GiantSignedBirthAddress B ell C batch),
        (σ.sign : ℤ) * (if GiantSignedBirthPermutationEvent d σ then 1 else 0) := by
  rw [giantSignedBirthDistinct_iff_performedInjective]
  exact markedBirthDistinct_permutation_sum _

theorem giantSignedBirthDistinct_weighted_sum (d : GiantSignedBirthData P ell C batch) (z : ℂ) :
    (if GiantSignedBirthDistinct d then z else 0) =
      ∑ σ : Equiv.Perm (GiantSignedBirthAddress B ell C batch),
        (σ.sign : ℂ) * (if GiantSignedBirthPermutationEvent d σ then z else 0) := by
  have h := congrArg (fun a : ℤ => (a : ℂ)) (giantSignedBirthDistinct_permutation_sum d)
  push_cast at h
  have hmul := congrArg (fun a : ℂ => a * z) h
  simpa only [Finset.sum_mul, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero] using hmul

theorem giantSignedBirthPermutationEvent_performed (d : GiantSignedBirthData P ell C batch)
    (σ : Equiv.Perm (GiantSignedBirthAddress B ell C batch))
    (hσ : GiantSignedBirthPermutationEvent d σ)
    (a : GiantSignedBirthAddress B ell C batch) (ha : a ∈ σ.support) :
    giantSignedBirthValue d a ≠ none :=
  markedBirthPermutationEvent_performed _ σ hσ a ha

omit [Fintype B] [DecidableEq B] in
theorem giantSignedBirthPermutationEvent_value (d : GiantSignedBirthData P ell C batch)
    (σ : Equiv.Perm (GiantSignedBirthAddress B ell C batch))
    (hσ : GiantSignedBirthPermutationEvent d σ)
    (a : GiantSignedBirthAddress B ell C batch) :
    giantSignedBirthValue d (σ a) = giantSignedBirthValue d a :=
  markedBirthPermutationEvent_value _ σ hσ a

theorem giantSignedBirthPermutation_operations_le
    (σ : Equiv.Perm (GiantSignedBirthAddress B ell C batch)) :
    (σ.support.image (giantSignedBirthOperation ell C batch)).card ≤
      2 * markedBirthPermutationRank σ :=
  markedBirthPermutation_operations_le_twice_rank _ σ

omit [DecidableEq B] in
theorem giantSignedBirthAddress_card :
    Fintype.card (GiantSignedBirthAddress B ell C batch) =
      Fintype.card B * (k+ell) +
        (∑ i : Fin n, ∑ g : B, (ell + (C i g).card)) +
        ∑ i : Fin (n+1), ∑ g : B, batch i g := by
  simp only [GiantSignedBirthAddress, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_sigma]
  omega

omit [DecidableEq B] in
theorem giantSignedBirthAddress_card_le (H : ℕ)
    (hbatch : ∀ i g, batch i g ≤ H) :
    Fintype.card (GiantSignedBirthAddress B ell C batch) ≤
      (n+1) * Fintype.card B * (k+ell+H) := by
  rw [giantSignedBirthAddress_card]
  have hc : (∑ i : Fin n, ∑ g : B, (ell + (C i g).card)) ≤
      n * (Fintype.card B * (k+ell)) := by
    calc
      _ ≤ ∑ _i : Fin n, ∑ _g : B, (k+ell) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro g _
        have h := Finset.card_le_card (Finset.subset_univ (C i g))
        simp only [Finset.card_univ, Fintype.card_fin] at h
        omega
      _ = _ := by simp
  have hb : (∑ i : Fin (n+1), ∑ g : B, batch i g) ≤
      (n+1) * (Fintype.card B * H) := by
    calc
      _ ≤ ∑ _i : Fin (n+1), ∑ _g : B, H := by
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun g _ => hbatch i g
      _ = _ := by simp
  calc
    _ ≤ Fintype.card B * (k+ell) + n * (Fintype.card B * (k+ell)) +
        (n+1) * (Fintype.card B * H) := Nat.add_le_add (Nat.add_le_add_left hc _) hb
    _ = _ := by ring

theorem giantSignedBirthPermutation_rank_card (r : ℕ) :
    Fintype.card {σ : Equiv.Perm (GiantSignedBirthAddress B ell C batch) //
      markedBirthPermutationRank σ = r} ≤
        (Fintype.card (GiantSignedBirthAddress B ell C batch) ^ 2 + 1) ^ (2*r) := by
  simpa only [pow_two] using
    markedBirthPermutation_rank_card_bound (A := GiantSignedBirthAddress B ell C batch) r

end
end ArtinMatthews
