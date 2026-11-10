module

public import ArtinMatthews.QuadraticHeckeFiniteEnergy
public import Mathlib.Analysis.Complex.Basic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.QuadraticScale
open scoped BigOperators
noncomputable section

variable {ι : Type*}

/-- Any selected set of coefficient pairs satisfies the same finite Cauchy bound. -/
theorem pairCoefficientMass_le (D : Finset ι) (pairs : Finset (ι × ι))
    (hpairs : pairs ⊆ D ×ˢ D) (a : ι → ℂ) :
    (∑ p ∈ pairs, ‖star (a p.1) * a p.2‖) ≤ (D.card : ℝ) * coeffMass D a := by
  calc
    _ ≤ ∑ p ∈ D ×ˢ D, ‖star (a p.1) * a p.2‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hpairs (fun _ _ _ => norm_nonneg _)
    _ = (∑ b ∈ D, ‖a b‖) ^ 2 := by
      calc
        _ = ∑ b ∈ D, ‖a b‖ * (∑ c ∈ D, ‖a c‖) := by
          rw [Finset.sum_product]
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c _
          rw [norm_mul, norm_star]
        _ = _ := by rw [← Finset.sum_mul, pow_two]
    _ ≤ _ := by
      simpa [coeffMass] using
        (Finset.sum_mul_sq_le_sq_mul_sq D (fun _ : ι => (1 : ℝ)) (fun b => ‖a b‖))

end
end ArtinMatthews.QuadraticScale
