module

public import ArtinMatthews.IdealFiniteFrame


set_option backward.privateInPublic true
@[expose] public section

/-! Finite weighted Hilbert--Schmidt Cauchy--Schwarz for arbitrary full
source and target tests. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [Fintype B]

theorem idealKernel_bilinear_sq_le (μ : A → ℝ) (ν : B → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b)
    (K : A → B → ℂ) (f : A → ℂ) (g : B → ℂ) :
    ‖∑ a, ∑ b, ((μ a*ν b : ℝ) : ℂ) * K a b * f a * g b‖^2 ≤
      (∑ a, ∑ b, μ a*ν b*‖K a b‖^2) * idealFrameEnergy μ f * idealFrameEnergy ν g := by
  let w : A × B → ℝ := fun z => μ z.1*ν z.2
  have hw (z : A × B) : 0 ≤ w z := mul_nonneg (hμ z.1) (hν z.2)
  have hc := idealFrame_weighted_cauchy w hw (fun z => star (K z.1 z.2))
    (fun z => f z.1*g z.2)
  have he : (∑ z : A × B, (w z : ℂ) * star (star (K z.1 z.2)) * (f z.1*g z.2)) =
      ∑ a, ∑ b, ((μ a*ν b : ℝ) : ℂ) * K a b * f a * g b := by
    simp only [Fintype.sum_prod_type, w, star_star]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    ring
  have henergy : idealFrameEnergy w (fun z => f z.1*g z.2) =
      idealFrameEnergy μ f * idealFrameEnergy ν g := by
    simp only [idealFrameEnergy, w, Fintype.sum_prod_type, norm_mul, mul_pow, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    ring
  rw [he, henergy] at hc
  simpa only [idealFrameEnergy, Fintype.sum_prod_type, w, norm_star, mul_assoc] using hc

end
end ArtinMatthews
