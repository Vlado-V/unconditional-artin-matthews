module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! A function with one-coordinate interpolation is determined by its
values on the finite product of the coordinate samples. -/
namespace ArtinMatthews

open scoped BigOperators

theorem sourceRetainedFiniteInterpolation
    {I : Type*} [Fintype I] [DecidableEq I]
    {G K : I → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
    (b : ∀ i, K i → G i) (c : ∀ i, K i → G i → ℂ) (A : (∀ i, G i) → ℂ)
    (hcoord : ∀ i (j k : K i), c i j (b i k) = if j = k then 1 else 0)
    (hexpand : ∀ g i, A g = ∑ j : K i, A (Function.update g i (b i j)) * c i j (g i))
    (g : ∀ i, G i) :
    A g = ∑ k : (∀ i, K i), A (fun i => b i (k i)) * ∏ i, c i (k i) (g i) := by
  let B : (∀ i, G i) → ℂ := fun g =>
    ∑ k : (∀ i, K i), A (fun i => b i (k i)) * ∏ i, c i (k i) (g i)
  have hBasis (k : ∀ i, K i) : B (fun i => b i (k i)) = A (fun i => b i (k i)) := by
    dsimp only [B]
    rw [Finset.sum_eq_single k]
    · simp only [hcoord, ite_true, Finset.prod_const_one, mul_one]
    · intro l _ hl
      have hi : ∃ i, l i ≠ k i := by
        classical
        by_contra hn
        apply hl
        funext i
        exact not_ne_iff.mp (fun h => hn ⟨i,h⟩)
      obtain ⟨i,hi⟩ := hi
      have hz : c i (l i) (b i (k i)) = 0 := by rw [hcoord, ite_eq_right hi]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, mul_zero]
    · exact fun h => (h (Finset.mem_univ k)).elim
  have hExpandB (g : ∀ i, G i) (i : I) :
      B g = ∑ j : K i, B (Function.update g i (b i j)) * c i j (g i) := by
    simp only [B, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_eq_single (k i)]
    · let p : I → ℂ := fun j => c j (k j) (Function.update g i (b i (k i)) j)
      let q : I → ℂ := fun j => c j (k j) (g j)
      have hAt : p i = 1 := by simp only [p, Function.update_self, hcoord, ite_true]
      have hErase : (∏ j ∈ Finset.univ.erase i, p j) = ∏ j ∈ Finset.univ.erase i, q j := by
        apply Finset.prod_congr rfl
        intro j hj
        exact congrArg (c j (k j)) (Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _)
      have hpq : (∏ j, p j) * q i = ∏ j, q j := by
        calc
          _ = ((∏ j ∈ Finset.univ.erase i, p j) * p i) * q i := by
            rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
          _ = (∏ j ∈ Finset.univ.erase i, q j) * q i := by rw [hAt, hErase, mul_one]
          _ = _ := Finset.prod_erase_mul _ _ (Finset.mem_univ i)
      change A (fun j => b j (k j)) * (∏ j, q j) =
        (A (fun j => b j (k j)) * (∏ j, p j)) * q i
      rw [mul_assoc, hpq]
    · intro j _ hj
      have hz : c i (k i) (Function.update g i (b i j) i) = 0 := by
        rw [Function.update_self, hcoord, ite_eq_right hj.symm]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, mul_zero, zero_mul]
    · exact fun h => (h (Finset.mem_univ (k i))).elim
  have hAll (s : Finset I) :
      ∀ g, (∀ i, i ∉ s → ∃ j : K i, g i = b i j) → A g = B g := by
    induction s using Finset.induction_on with
    | empty =>
        intro g hg
        choose k hk using fun i => hg i (Finset.notMem_empty i)
        rw [show g = (fun i => b i (k i)) from funext hk, hBasis]
    | insert i s hi ih =>
        intro g hg
        rw [hexpand g i, hExpandB g i]
        apply Finset.sum_congr rfl
        intro j _
        have hUpdated (l : I) (hl : l ∉ s) :
            ∃ k : K l, Function.update g i (b i j) l = b l k := by
          by_cases hli : l = i
          · subst l
            exact ⟨j, Function.update_self i _ _⟩
          · rw [Function.update_of_ne hli]
            exact hg l (by simp only [Finset.mem_insert, hli, hl, or_self, not_false_eq_true])
        rw [ih _ hUpdated]
  exact hAll Finset.univ g (fun i hi => (hi (Finset.mem_univ i)).elim)

end ArtinMatthews
