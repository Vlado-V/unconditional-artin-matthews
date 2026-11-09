module

public import ArtinMatthews.MarkedFiniteCells


set_option backward.privateInPublic true
@[expose] public section

/-! Position-preserving matrices keep an actual cell bandwidth under
left and right multiplication. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical
noncomputable section

theorem markedMatrix_mul_ne_zero {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) (s t : ι) (h : (A*B) s t≠0) :
    ∃ u, A s u≠0 ∧ B u t≠0 := by
  by_contra hn
  apply h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro u _
  by_cases ha : A s u=0
  · rw [ha,zero_mul]
  · have hb : B u t=0 := by
      by_contra hb
      exact hn ⟨u,ha,hb⟩
    rw [hb,mul_zero]

theorem markedMatrix_bandwidth_mul_left {ι κ : Type*} [Fintype ι]
    (A S : Matrix ι ι ℂ) (p : ι → κ) (c : κ → ℤ) (R : ℤ)
    (hA : ∀ s t, A s t≠0 → c (p t)-c (p s) ∈ Finset.Icc (-R) R)
    (hS : ∀ s t, S s t≠0 → p s=p t) :
    ∀ s t, (S*A) s t≠0 → c (p t)-c (p s) ∈ Finset.Icc (-R) R := by
  intro s t h
  obtain ⟨u,hs,ha⟩ := markedMatrix_mul_ne_zero S A s t h
  rw [hS s u hs]
  exact hA u t ha

theorem markedMatrix_bandwidth_mul_right {ι κ : Type*} [Fintype ι]
    (A S : Matrix ι ι ℂ) (p : ι → κ) (c : κ → ℤ) (R : ℤ)
    (hA : ∀ s t, A s t≠0 → c (p t)-c (p s) ∈ Finset.Icc (-R) R)
    (hS : ∀ s t, S s t≠0 → p s=p t) :
    ∀ s t, (A*S) s t≠0 → c (p t)-c (p s) ∈ Finset.Icc (-R) R := by
  intro s t h
  obtain ⟨u,ha,hs⟩ := markedMatrix_mul_ne_zero A S s t h
  rw [← hS u t hs]
  exact hA s u ha

theorem markedMatrix_diagonal_preserves_position {ι κ : Type*} [DecidableEq ι]
    (d : ι → ℂ) (p : ι → κ) (s t : ι) (h : Matrix.diagonal d s t≠0) : p s=p t := by
  have he : s=t := by
    by_contra hn
    exact h (Matrix.diagonal_apply_ne _ hn)
  exact congrArg p he

end
end ArtinMatthews
