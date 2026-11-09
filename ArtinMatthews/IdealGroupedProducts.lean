module

public import ArtinMatthews.IdealSelectedLabels
public import Mathlib.Data.Nat.Factors
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.List.Permutation


set_option backward.privateInPublic true
@[expose] public section

/-! Numeric products determine the prime multiset in each disjoint band,
while every repeated label and its original order remain in the carrier. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev IdealGroupedLabels {J : Type*} (P : J → Finset ℕ) (k : J → ℕ) :=
  ∀ j, Fin (k j) → ↥(P j)

def idealGroupProduct {J : Type*} {P : J → Finset ℕ} {k : J → ℕ}
    (a : IdealGroupedLabels P k) (j : J) : ℕ :=
  ∏ i, (a j i).val

def idealGroupedProduct {J : Type*} [Fintype J] {P : J → Finset ℕ} {k : J → ℕ}
    (a : IdealGroupedLabels P k) : ℕ :=
  ∏ j, idealGroupProduct a j

theorem idealGroupProduct_pos {J : Type*} {P : J → Finset ℕ} {k : J → ℕ}
    (hP : ∀ j p, p ∈ P j → p.Prime) (a : IdealGroupedLabels P k) (j : J) :
    0 < idealGroupProduct a j :=
  prod_pos fun i _ => (hP j _ (a j i).property).pos

theorem idealGroupProduct_coprime {J : Type*} {P : J → Finset ℕ} {k : J → ℕ}
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (a b : IdealGroupedLabels P k) {j l : J} (hjl : j ≠ l) :
    (idealGroupProduct a j).Coprime (idealGroupProduct b l) := by
  apply Nat.coprime_prod_left_iff.mpr
  intro i _
  apply Nat.coprime_prod_right_iff.mpr
  intro t _
  apply (Nat.coprime_primes (hP j _ (a j i).property) (hP l _ (b l t).property)).mpr
  intro he
  have hp := (Finset.disjoint_left.mp (hdis hjl)) (a j i).property
  exact hp (he ▸ (b l t).property)

theorem idealGroupedProduct_recover {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k : J → ℕ}
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (a b : IdealGroupedLabels P k) (he : idealGroupedProduct a = idealGroupedProduct b)
    (j : J) : idealGroupProduct a j = idealGroupProduct b j := by
  have hdvd (a b : IdealGroupedLabels P k)
      (he : idealGroupedProduct a = idealGroupedProduct b) :
      idealGroupProduct a j ∣ idealGroupProduct b j := by
    have hc : (idealGroupProduct a j).Coprime
        (∏ l : {l : J // l ≠ j}, idealGroupProduct b l.val) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro l _
      exact idealGroupProduct_coprime hP hdis a b (Ne.symm l.property)
    apply hc.dvd_of_dvd_mul_right
    rw [← Fintype.prod_eq_mul_prod_subtype_ne]
    change idealGroupProduct a j ∣ idealGroupedProduct b
    rw [← he]
    exact dvd_prod_of_mem _ (mem_univ j)
  exact Nat.dvd_antisymm (hdvd a b he) (hdvd b a he.symm)

def idealGroupWord {J : Type*} {P : J → Finset ℕ} {k : J → ℕ}
    (a : IdealGroupedLabels P k) (j : J) : List ℕ :=
  List.ofFn (fun i => (a j i).val)

theorem idealGroupWord_prod {J : Type*} {P : J → Finset ℕ} {k : J → ℕ}
    (a : IdealGroupedLabels P k) (j : J) :
    (idealGroupWord a j).prod = idealGroupProduct a j := by
  simp only [idealGroupWord, List.prod_ofFn, idealGroupProduct]

theorem idealGroupedProduct_word_perm {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k : J → ℕ}
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (a b : IdealGroupedLabels P k) (he : idealGroupedProduct a = idealGroupedProduct b)
    (j : J) : (idealGroupWord a j).Perm (idealGroupWord b j) := by
  have ha : (idealGroupWord a j).Perm (idealGroupProduct a j).primeFactorsList :=
    Nat.primeFactorsList_unique (idealGroupWord_prod a j) (by
      intro p hp
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
      exact hP j _ (a j i).property)
  have hb : (idealGroupWord b j).Perm (idealGroupProduct b j).primeFactorsList :=
    Nat.primeFactorsList_unique (idealGroupWord_prod b j) (by
      intro p hp
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
      exact hP j _ (b j i).property)
  rw [idealGroupedProduct_recover hP hdis a b he j] at ha
  exact ha.trans hb.symm

end
end ArtinMatthews
