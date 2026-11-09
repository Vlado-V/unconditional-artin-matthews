module

public import ArtinMatthews.SpectralSquareProfile
public import ArtinMatthews.SpectralJGaussianFubini


set_option backward.privateInPublic true
@[expose] public section

/-! The actual forward-J transform in the squared coordinate. -/
namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

theorem spectralJGaussianTransform_square (g : ℝ → ℂ) (w : ℝ) :
    spectralJGaussianTransform (fun x : ℝ => (x : ℂ) * g (x ^ 2)) w =
      (1 / 2 : ℂ) * ∫ s : ℝ in Ioi 0, g s * spectralJGaussianKernel (Real.sqrt s) w := by
  let k (s : ℝ) := g s * spectralJGaussianKernel (Real.sqrt s) w
  calc
    _ = ∫ x : ℝ in Ioi 0, (x : ℂ) * k (x ^ 2) := by
      unfold spectralJGaussianTransform
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx₀ : 0 ≤ x := (mem_Ioi.mp hx).le
      dsimp only [k]
      rw [Real.sqrt_sq hx₀, mul_assoc]
    _ = _ := spectralSquare_integral k

theorem spectralJGaussianTransform_squareProfile (f : ℝ → ℂ) (w : ℝ) :
    spectralJGaussianTransform f w =
      (1 / 2 : ℂ) * ∫ s : ℝ in Ioi 0,
        spectralSquareProfile f s * spectralJGaussianKernel (Real.sqrt s) w := by
  calc
    _ = spectralJGaussianTransform (fun x : ℝ => (x : ℂ) * spectralSquareProfile f (x ^ 2)) w := by
      unfold spectralJGaussianTransform
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [spectralSquareProfile_recovery f (mem_Ioi.mp hx)]
    _ = _ := spectralJGaussianTransform_square _ _

end
end ArtinMatthews
