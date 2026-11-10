module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! A retrieved degree is removed from every finite group. The exact
degree reindexing retains all degrees for which a retrieval can exist. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def giantSignedDegreeShiftEquiv {J : Type*} (a : J → ℕ) :
    (J → ℕ) ≃ {k : J → ℕ // ∀ j, a j ≤ k j} where
  toFun n := ⟨fun j => n j + a j, fun j => Nat.le_add_left _ _⟩
  invFun k j := k.val j - a j
  left_inv n := by
    funext j
    exact Nat.add_sub_cancel_right (n j) (a j)
  right_inv k := by
    apply Subtype.ext
    funext j
    exact Nat.sub_add_cancel (k.property j)

theorem giantSignedDegreeShift_tsum {J E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (a : J → ℕ) (F : (J → ℕ) → E)
    (hzero : ∀ k, ¬ (∀ j, a j ≤ k j) → F k = 0) :
    (∑' k, F k) = ∑' n : J → ℕ, F (fun j => n j + a j) := by
  have hs : Function.support F ⊆ {k : J → ℕ | ∀ j, a j ≤ k j} := by
    intro k hk
    change F k ≠ 0 at hk
    by_contra h
    exact hk (hzero k h)
  calc
    _ = ∑' k : {k : J → ℕ // ∀ j, a j ≤ k j}, F k.val :=
      (tsum_subtype_eq_of_support_subset hs).symm
    _ = _ := ((giantSignedDegreeShiftEquiv a).tsum_eq (fun k => F k.val)).symm

end
end ArtinMatthews
