module

public import ArtinMatthews.IdealGroupedProducts


set_option backward.privateInPublic true
@[expose] public section

/-! Each numeric-product fiber is contained in the actual per-group
permutation family. Repeated labels reduce its size. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]

abbrev IdealGroupedFiber (P : J → Finset ℕ) (k : J → ℕ) (n : ℕ) :=
  {a : IdealGroupedLabels P k // idealGroupedProduct a = n}

def idealGroupedFiberWords {P : J → Finset ℕ} {k : J → ℕ}
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (a : IdealGroupedLabels P k)
    (b : IdealGroupedFiber P k (idealGroupedProduct a)) :
    ∀ j, ↥((idealGroupWord a j).permutations.toFinset) := fun j =>
  ⟨idealGroupWord b.val j, List.mem_toFinset.mpr (List.mem_permutations.mpr
    (idealGroupedProduct_word_perm hP hdis b.val a b.property j))⟩

theorem idealGroupedFiberWords_injective {P : J → Finset ℕ} {k : J → ℕ}
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (a : IdealGroupedLabels P k) :
    Function.Injective (idealGroupedFiberWords hP hdis a) := by
  intro b c he
  apply Subtype.ext
  funext j i
  apply Subtype.ext
  have hl : idealGroupWord b.val j = idealGroupWord c.val j :=
    congrArg Subtype.val (congrFun he j)
  exact congrFun (List.ofFn_injective hl) i

theorem idealGroupedProduct_fiber_card_le {P : J → Finset ℕ} {k : J → ℕ}
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (n : ℕ) :
    Fintype.card (IdealGroupedFiber P k n) ≤ ∏ j, (k j).factorial := by
  by_cases hne : Nonempty (IdealGroupedFiber P k n)
  · obtain ⟨a⟩ := hne
    have hn : n = idealGroupedProduct a.val := a.property.symm
    rw [hn]
    calc
      _ ≤ Fintype.card (∀ j, ↥((idealGroupWord a.val j).permutations.toFinset)) :=
        Fintype.card_le_of_injective _ (idealGroupedFiberWords_injective hP hdis a.val)
      _ = ∏ j, ((idealGroupWord a.val j).permutations.toFinset).card := by simp
      _ ≤ ∏ j, (k j).factorial := by
        apply prod_le_prod
        intro j _
        calc
          _ ≤ ((idealGroupWord a.val j).permutations).length := List.toFinset_card_le _
          _ = (k j).factorial := by rw [List.length_permutations]; simp [idealGroupWord]
  · let : IsEmpty (IdealGroupedFiber P k n) := ⟨fun a => hne ⟨a⟩⟩
    simp only [Fintype.card_of_isEmpty]
    exact Nat.zero_le _

end
end ArtinMatthews
