module

public import ArtinMatthews.SourceArchSphericalRightCasimir


set_option backward.privateInPublic true
@[expose] public section

/-! Radial multiplication along the actual logarithmic height paths. -/

namespace ArtinMatthews.SourceArchJacquet
open scoped ContDiff
noncomputable section

def sourceKPRadialPath (φ H : ℝ → ℝ) (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  (φ (H t) : ℂ) * F t

def sourceKPRadialPathOne (φ H L : ℝ → ℝ) (β : ℂ) (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  ((2*H t*deriv φ (H t) : ℝ) + β*(φ (H t) : ℂ)) * (L t : ℂ) * F t

def sourceKPRadialPathTwo (φ H L M : ℝ → ℝ) (β : ℂ) (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  (((4*(H t)^2*deriv (deriv φ) (H t) : ℝ) +
      4*(β+1)*(H t : ℂ)*((deriv φ (H t) : ℝ) : ℂ) + β^2*(φ (H t) : ℂ)) * (L t : ℂ)^2 +
    ((2*H t*deriv φ (H t) : ℝ) + β*(φ (H t) : ℂ)) * (M t : ℂ)) * F t

theorem sourceKPRadialPath_hasDerivAt
    (φ H L : ℝ → ℝ) (β : ℂ) (F : ℝ → ℂ) (t : ℝ)
    (hφ : DifferentiableAt ℝ φ (H t))
    (hH : HasDerivAt H (2*H t*L t) t)
    (hF : HasDerivAt F (β*(L t : ℂ)*F t) t) :
    HasDerivAt (sourceKPRadialPath φ H F) (sourceKPRadialPathOne φ H L β F t) t := by
  have h := ((hφ.hasDerivAt.comp t hH).ofReal_comp).mul hF
  convert h using 1
  · rfl
  · simp only [sourceKPRadialPathOne,Function.comp_def]
    push_cast
    ring

theorem sourceKPRadialPathOne_hasDerivAt
    (φ H L M : ℝ → ℝ) (β : ℂ) (F : ℝ → ℂ) (t : ℝ)
    (hφ : ContDiff (ℝ) (2 : ℕ∞ω) φ)
    (hH : HasDerivAt H (2*H t*L t) t)
    (hL : HasDerivAt L (M t) t)
    (hF : HasDerivAt F (β*(L t : ℂ)*F t) t) :
    HasDerivAt (sourceKPRadialPathOne φ H L β F)
      (sourceKPRadialPathTwo φ H L M β F t) t := by
  have hφ₀ := (hφ.differentiable (by norm_num)).differentiableAt.hasDerivAt.comp t hH
  have hφ₁ := ((hφ.deriv' : ContDiff (ℝ) (1 : ℕ∞ω) (deriv φ)).differentiable
    (by norm_num)).differentiableAt.hasDerivAt.comp t hH
  have h := ((((hH.const_mul 2).mul hφ₁).ofReal_comp).add
    (hφ₀.ofReal_comp.const_mul β)).mul hL.ofReal_comp |>.mul hF
  convert h using 1
  · rfl
  · simp only [sourceKPRadialPathTwo,Function.comp_def,Pi.mul_apply,Pi.add_apply]
    push_cast
    ring

theorem sourceKPRadialPath_deriv_two
    (φ H L M : ℝ → ℝ) (β : ℂ) (F : ℝ → ℂ) (t : ℝ)
    (hφ : ContDiff (ℝ) (2 : ℕ∞ω) φ)
    (hH : ∀ u, HasDerivAt H (2*H u*L u) u)
    (hL : ∀ u, HasDerivAt L (M u) u)
    (hF : ∀ u, HasDerivAt F (β*(L u : ℂ)*F u) u) :
    deriv (deriv (sourceKPRadialPath φ H F)) t = sourceKPRadialPathTwo φ H L M β F t := by
  have he : deriv (sourceKPRadialPath φ H F) = sourceKPRadialPathOne φ H L β F := by
    funext u
    exact (sourceKPRadialPath_hasDerivAt φ H L β F u
      ((hφ.differentiable (by norm_num)).differentiableAt) (hH u) (hF u)).deriv
  rw [he]
  exact (sourceKPRadialPathOne_hasDerivAt φ H L M β F t hφ (hH t) (hL t) (hF t)).deriv

def sourceKPRadialUpperHeight (A : ℝ) (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) : ℝ :=
  A * (sourceArchHeight (g*sourceKPUpperMatrix ℂ ((t : ℂ)*z)))^2

def sourceKPRadialDiagonalHeight (A : ℝ) (g : GL (Fin 2) ℂ) (t : ℝ) : ℝ :=
  A * (sourceArchHeight (g*sourceArchPositiveDiagonal t))^2

theorem sourceKPRadialUpperHeight_hasDerivAt (A : ℝ) (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    HasDerivAt (sourceKPRadialUpperHeight A g z)
      (2*sourceKPRadialUpperHeight A g z t*sourceArchUpperLogOne g z t) t := by
  have he : (fun u : ℝ => Real.exp (sourceArchUpperLog g z u)) =
      fun u : ℝ => sourceArchHeight (g*sourceKPUpperMatrix ℂ ((u : ℂ)*z)) := by
    funext u
    rw [sourceArchUpperLog_eq,Real.exp_log (sourceArchHeight_pos _)]
  have h := (((sourceArchUpperLog_hasDerivAt g z t).exp).pow 2).const_mul A
  rw [he] at h
  convert h using 1
  · rfl
  · unfold sourceKPRadialUpperHeight
    simp only [sourceArchUpperLog_eq,Real.exp_log (sourceArchHeight_pos _)]
    ring

theorem sourceKPRadialDiagonalHeight_hasDerivAt (A : ℝ) (g : GL (Fin 2) ℂ) (t : ℝ) :
    HasDerivAt (sourceKPRadialDiagonalHeight A g)
      (2*sourceKPRadialDiagonalHeight A g t*sourceArchDiagonalLogOne g t) t := by
  have he : (fun u : ℝ => Real.exp (sourceArchDiagonalLog g u)) =
      fun u : ℝ => sourceArchHeight (g*sourceArchPositiveDiagonal u) := by
    funext u
    rw [sourceArchDiagonalLog_eq,Real.exp_log (sourceArchHeight_pos _)]
  have h := (((sourceArchDiagonalLog_hasDerivAt g t).exp).pow 2).const_mul A
  rw [he] at h
  convert h using 1
  · rfl
  · unfold sourceKPRadialDiagonalHeight
    simp only [sourceArchDiagonalLog_eq,Real.exp_log (sourceArchHeight_pos _)]
    ring

end
end ArtinMatthews.SourceArchJacquet
