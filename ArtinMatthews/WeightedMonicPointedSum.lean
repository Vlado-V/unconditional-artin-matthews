module

public import ArtinMatthews.WeightedMonicPointing


set_option backward.privateInPublic true
@[expose] public section

/-! Sum the unique-factorization pointing identity over a finite monic
degree layer, retaining literal prime-power divisibility fibers. -/
namespace ArtinMatthews.WeightedMonic
noncomputable section
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F]

theorem coefficient_pointed_sum (w : F[X] → ℂ) (n : ℕ) :
    (n:ℂ)*coefficient w n =
      ∑ P ∈ atoms n, ∑ r ∈ Finset.Icc 1 n, (P.natDegree:ℂ)*
        ∑ Q ∈ layer n,if P^r ∣ Q then w Q else 0 := by
  rw [coefficient_sum,Finset.mul_sum]
  calc
    _ = ∑ Q ∈ layer n, ∑ P ∈ atoms n, ∑ r ∈ Finset.Icc 1 n,
        if P^r ∣ Q then (P.natDegree:ℂ)*w Q else 0 := by
      apply Finset.sum_congr rfl
      intro Q hQ
      obtain ⟨hm,hd⟩ := (mem_layer n Q).mp hQ
      exact degree_pointed w hm hd
    _ = ∑ P ∈ atoms n, ∑ r ∈ Finset.Icc 1 n, ∑ Q ∈ layer n,
        if P^r ∣ Q then (P.natDegree:ℂ)*w Q else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro P _
      rw [Finset.sum_comm]
    _ = _ := by simp only [Finset.mul_sum,mul_ite,mul_zero]

end
end ArtinMatthews.WeightedMonic
