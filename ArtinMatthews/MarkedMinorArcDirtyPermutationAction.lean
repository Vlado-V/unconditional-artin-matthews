module

public import ArtinMatthews.MarkedMinorArcDirtyPermutation


set_option backward.privateInPublic true
@[expose] public section

/-! The literal permuted copied slots agree with the source omission coordinate. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem markedSourceCopiedProduct_permuted {J : Type*} [Fintype J] {M : ℕ}
    (source : J → Fin M → ℕ) (σ : J → Equiv.Perm (Fin M)) (choice : J → Fin M) :
    markedSourceCopiedProduct (fun j k => source j (σ j k)) choice =
      markedSourceCopiedProduct source (fun j => σ j (choice j)) := by
  unfold markedSourceCopiedProduct
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_bij (fun k _ => σ j k)
  · intro k hk
    exact Finset.mem_erase.mpr
      ⟨fun he => (Finset.mem_erase.mp hk).1 ((σ j).injective he), Finset.mem_univ _⟩
  · intro k _ l _ he
    exact (σ j).injective he
  · intro l hl
    refine ⟨(σ j).symm l, Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩, (σ j).apply_symm_apply l⟩
    intro he
    have hh := congrArg (σ j) he
    simp only [Equiv.apply_symm_apply] at hh
    exact (Finset.mem_erase.mp hl).1 hh
  · intro k _
    rfl

/-- This is the actual copied-slot product after independent uniform
permutations of every source list, including every internal slot order. -/
theorem markedSourcePermutedCopiedProduct_mass {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (P : J → Finset ℕ) (hprime : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (source : J → Fin (n+1) → ℕ) (hsource : ∀ j k, source j k ∈ P j)
    (hdist : ∀ j, Function.Injective (source j)) (slot : Fin (n+1)) (a : J → Fin (n+1)) :
    (∑ σ : J → Equiv.Perm (Fin (n+1)),
      if markedSourceCopiedProduct (fun j k => source j (σ j k)) (fun _ => slot) =
          markedSourceCopiedProduct source a then
        ∏ _j : J, 1/(Fintype.card (Equiv.Perm (Fin (n+1))):ℝ) else 0) =
      (n+1:ℝ)⁻¹^(Fintype.card J) := by
  simp_rw [markedSourceCopiedProduct_permuted]
  exact markedSourceCopiedProduct_permutation_mass n P hprime hdis source hsource hdist slot a

end ArtinMatthews
