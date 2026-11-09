module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceArchJacquet

theorem sourceArch_log_lipschitz {L D : ℝ → ℝ} {C : ℝ}
    (hL : ∀ t, HasDerivAt L (D t) t) (hD : ∀ t, |D t| ≤ C) (t u : ℝ) :
    |L t-L u| ≤ C*|t-u| := by
  have hd : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ L x :=
    fun x _ => (hL x).differentiableAt
  have hb : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv L x‖ ≤ C := by
    intro x _
    rw [(hL x).deriv, Real.norm_eq_abs]
    exact hD x
  simpa only [Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      hd hb (Set.mem_univ u) (Set.mem_univ t)

theorem sourceArch_log_profile_bound {l l₀ σ B D : ℝ}
    (hL : |l-l₀| ≤ D) (hσ : |σ| ≤ B) :
    Real.exp (l*σ) ≤ Real.exp (B*D) * Real.exp (l₀*σ) := by
  have hb : 0 ≤ B := (abs_nonneg σ).trans hσ
  have hprod : σ*(l-l₀) ≤ B*D := by
    calc
      _ ≤ |σ*(l-l₀)| := le_abs_self _
      _ = |σ| * |l-l₀| := abs_mul _ _
      _ ≤ B*D := mul_le_mul hσ hL (abs_nonneg _) hb
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hprod]

end ArtinMatthews.SourceArchJacquet
