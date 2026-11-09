module

public import OAI.Analysis.PDE.Weak.Elliptic.SmoothBounded


set_option backward.privateInPublic true
@[expose] public section

/-! Exact cutoff differentiation identities for the quantitative H2 estimate. -/
noncomputable section
open scoped ContDiff
open OAI.Analysis.PDE.Weak
namespace ArtinMatthews

theorem spectral_coordinateDerivative_mul {F G : (Fin 2 → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (j : Fin 2) :
    coordinateDerivative (fun x => F x*G x) j =
      fun x => coordinateDerivative F j x*G x+F x*coordinateDerivative G j x := by
  funext x
  unfold coordinateDerivative
  rw [fderiv_fun_mul (hF.differentiable (by simp) x) (hG.differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

theorem spectral_coordinateDerivative_add {F G : (Fin 2 → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (j : Fin 2) :
    coordinateDerivative (fun x => F x+G x) j =
      fun x => coordinateDerivative F j x+coordinateDerivative G j x := by
  funext x
  unfold coordinateDerivative
  rw [fderiv_fun_add (hF.differentiable (by simp) x) (hG.differentiable (by simp) x)]
  rfl

theorem spectral_coordinate_mixed_cutoff_square {η u : (Fin 2 → ℝ) → ℝ}
    (hη : ContDiff ℝ ∞ η) (hu : ContDiff ℝ ∞ u) (x : Fin 2 → ℝ) :
    coordinateDerivative (coordinateDerivative (η*(η*u)) 0) 1 x =
      η x*coordinateDerivative (η*coordinateDerivative u 0) 1 x +
      η x*coordinateDerivative η 1 x*coordinateDerivative u 0 x +
      2*η x*coordinateDerivative η 0 x*coordinateDerivative u 1 x +
      2*(coordinateDerivative η 1 x*coordinateDerivative η 0 x+
        η x*coordinateDerivative (coordinateDerivative η 0) 1 x)*u x := by
  have hη0 := contDiff_coordinateDerivative hη (0 : Fin 2)
  have hu0 := contDiff_coordinateDerivative hu (0 : Fin 2)
  simp only [Pi.mul_def]
  simp (disch := fun_prop) only [spectral_coordinateDerivative_mul,spectral_coordinateDerivative_add]
  ring

end ArtinMatthews
