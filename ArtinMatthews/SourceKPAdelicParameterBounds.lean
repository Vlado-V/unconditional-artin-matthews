module

public import ArtinMatthews.SourceKPAdelicFlatSection
public import ArtinMatthews.SourceKPAdelicConstantTermPeriodization


set_option backward.privateInPublic true
@[expose] public section

/-! Two real parameter values dominate the actual flat section on the
whole vertical strip between them. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCompactScalar_norm_le_endpoints (a b : ℝ) (s : ℂ)
    (hs : a ≤ s.re ∧ s.re ≤ b) (q : SourceKPAdelicProjective K hζ) :
    ‖sourceKPAdelicCompactScalar K hζ s q‖ ≤
      ‖sourceKPAdelicCompactScalar K hζ (a : ℂ) q‖ +
        ‖sourceKPAdelicCompactScalar K hζ (b : ℂ) q‖ := by
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  rw [sourceKPAdelicCompactScalar_norm_flat K hζ s q g hg.symm,
    sourceKPAdelicCompactScalar_norm_flat K hζ (a : ℂ) q g hg.symm,
    sourceKPAdelicCompactScalar_norm_flat K hζ (b : ℂ) q g hg.symm]
  simp only [Complex.ofReal_re]
  by_cases hlog : 0 ≤ Real.log (sourceKPAdelicHeight K hζ g)
  · calc
      _ ≤ Real.exp (b*Real.log (sourceKPAdelicHeight K hζ g)) *
          ‖sourceKPAdelicCompactScalar K hζ 0 q‖ :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs.2 hlog))
          (norm_nonneg _)
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  · calc
      _ ≤ Real.exp (a*Real.log (sourceKPAdelicHeight K hζ g)) *
          ‖sourceKPAdelicCompactScalar K hζ 0 q‖ :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonpos_right hs.1 (le_of_not_ge hlog))) (norm_nonneg _)
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))

theorem sourceKPAdelicIntertwiningKernel_norm_le_endpoints (a b : ℝ) (s : ℂ)
    (hs : a ≤ s.re ∧ s.re ≤ b) (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) :
    ‖sourceKPAdelicIntertwiningKernel K hζ s g y‖ ≤
      ‖sourceKPAdelicIntertwiningKernel K hζ (a : ℂ) g y‖ +
        ‖sourceKPAdelicIntertwiningKernel K hζ (b : ℂ) g y‖ :=
  sourceKPAdelicCompactScalar_norm_le_endpoints K hζ a b s hs _

end
end ArtinMatthews
