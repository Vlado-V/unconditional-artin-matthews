module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFixedCode


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite reindexings used by the actual delta edge row. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedDirtyPromotionTupleErase {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B} {I : Finset J}
    (t : MarkedRawPromotionTuple m I) (jstar : J) : MarkedRawPromotionTuple m (I.erase jstar) :=
  fun j => t ⟨j.1,(Finset.mem_erase.mp j.2).2⟩

def markedDirtyPromotionTupleSplit {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B) (I : Finset J)
    (jstar : J) (hstar : jstar ∈ I) :
    MarkedRawPromotionTuple m I ≃ Fin (m.1.1 jstar:ℕ) × MarkedRawPromotionTuple m (I.erase jstar) where
  toFun t := (t ⟨jstar,hstar⟩,markedDirtyPromotionTupleErase t jstar)
  invFun t j := if h : j.1=jstar then h.symm ▸ t.1 else
    t.2 ⟨j.1,Finset.mem_erase.mpr ⟨h,j.2⟩⟩
  left_inv t := by
    funext j
    dsimp only
    split_ifs with h
    · cases h
      rfl
    · rfl
  right_inv t := by
    apply Prod.ext
    · simp
    · funext j
      have hn := (Finset.mem_erase.mp j.2).1
      simp only [markedDirtyPromotionTupleErase,dite_eq_right hn]

/-- Enlarging an actual finite injective image loses no index factor. -/
theorem markedDirtyFinite_sum_le_of_injective {α β : Type*} [Fintype α] [Fintype β]
    (e : α → β) (he : Function.Injective e) (f : α → ℝ) (g : β → ℝ)
    (hg : ∀ b, 0 ≤ g b) (hfg : ∀ a, f a ≤ g (e a)) : (∑ a, f a) ≤ ∑ b, g b := by
  classical
  calc
    _ ≤ ∑ a, g (e a) := Finset.sum_le_sum (fun a _ => hfg a)
    _ = ∑ b ∈ Finset.univ.image e, g b :=
      (Finset.sum_image (fun _ _ _ _ h => he h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hg b)

end ArtinMatthews
