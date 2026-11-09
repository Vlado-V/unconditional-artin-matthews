module

public import ArtinMatthews.GiantCandidateSquareCount
public import ArtinMatthews.GiantOrderedProductMoment
public import Mathlib.Analysis.Real.Sqrt


set_option backward.privateInPublic true
@[expose] public section

/-! The exceptional mass counts the actual positive ordered product fibers.
The divisor second moment follows from their factor refinement matrices. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

def giantCandidateSquareFiberMass (C : Finset ℕ) (X j : ℕ) : ℝ :=
  ∑ n ∈ giantCandidateSquareExceptions C X, ((giantOrderedProductFiber j n).card:ℝ)

theorem giantCandidateSquareFiberMass_nonneg (C : Finset ℕ) (X j : ℕ) :
    0 ≤ giantCandidateSquareFiberMass C X j := sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem giantCandidateSquareFiberMass_le (C : Finset ℕ) (X j : ℕ) :
    giantCandidateSquareFiberMass C X j ≤
      Real.sqrt ((giantCandidateSquareExceptions C X).card:ℝ) *
        Real.sqrt ((X:ℝ)*(1+Real.log (X:ℝ))^(j*j)) := by
  let D := giantCandidateSquareExceptions C X
  let f (n : ℕ) : ℝ := (giantOrderedProductFiber j n).card
  have hD : D ⊆ Ioc 0 X := fun n hn =>
    let h := mem_giantCandidateSquareExceptions.mp hn
    mem_Ioc.mpr ⟨h.1,h.2.1⟩
  change (∑ n ∈ D,f n) ≤ _
  calc
    _ ≤ Real.sqrt (D.card:ℝ) * Real.sqrt (∑ n ∈ D,(f n)^2) := by
      simpa only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] using
        Real.sum_mul_le_sqrt_mul_sqrt D (fun _ => 1) f
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      ((sum_le_sum_of_subset_of_nonneg hD (fun _ _ _ => sq_nonneg _)).trans
        (giant_ordered_product_fiber_second_moment j X))) (Real.sqrt_nonneg _)

theorem giantCandidateSquareFiberMass_eq_tuple_card (C : Finset ℕ) (X j : ℕ) :
    giantCandidateSquareFiberMass C X j =
      (((giantOrderedProductTuples j X).filter
        (fun t => ∃ p ∈ C,p^2 ∣ ∏ i,t i)).card:ℝ) := by
  let D := giantCandidateSquareExceptions C X
  let R := (giantOrderedProductTuples j X).filter (fun t => ∃ p ∈ C,p^2 ∣ ∏ i,t i)
  let g (t : Fin j → ℕ) := ∏ i,t i
  have hg : ∀ t ∈ R,g t ∈ D := by
    intro t ht
    obtain ⟨hT,hP⟩ := mem_filter.mp ht
    obtain ⟨hpos,hcap⟩ := mem_giantOrderedProductTuples.mp hT
    exact mem_giantCandidateSquareExceptions.mpr ⟨prod_pos (fun i _ => hpos i),hcap,hP⟩
  have hfib (n : ℕ) (hn : n ∈ D) : R.filter (fun t => g t=n) = giantOrderedProductFiber j n := by
    obtain ⟨_,hnX,hsq⟩ := mem_giantCandidateSquareExceptions.mp hn
    ext t
    simp only [R,mem_filter,mem_giantOrderedProductTuples,mem_giantOrderedProductFiber]
    constructor
    · exact fun h => ⟨h.1.1.1,h.2⟩
    · rintro ⟨hpos,hprod⟩
      have hcap : (∏ i,t i) ≤ X := hprod.le.trans hnX
      have hs : ∃ p ∈ C,p^2 ∣ ∏ i,t i := hprod ▸ hsq
      exact ⟨⟨⟨hpos,hcap⟩,hs⟩,hprod⟩
  change (∑ n ∈ D,((giantOrderedProductFiber j n).card:ℝ)) = (R.card:ℝ)
  calc
    _ = ∑ n ∈ D,∑ _t ∈ R.filter (fun t => g t=n),(1:ℝ) := by
      apply sum_congr rfl
      intro n hn
      simp only [hfib n hn,sum_const,nsmul_eq_mul,mul_one]
    _ = ∑ _t ∈ R,(1:ℝ) := sum_fiberwise_of_maps_to hg _
    _ = _ := by simp only [sum_const,nsmul_eq_mul,mul_one]

end
end ArtinMatthews
