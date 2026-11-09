module

public import ArtinMatthews.SourceEisensteinNonconstant
public import ArtinMatthews.SourceKPAdelicCutoffSupport


set_option backward.privateInPublic true
@[expose] public section

/-! The original Eisenstein-minus-cutoff function splits into its genuine nonconstant and outgoing terms. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicInitialDifference (T : ℝ) (s : ℂ) (q : SourceKPAdelicProjective K hζ) : ℂ :=
  sourceKPAdelicCompactEisenstein K hζ s q - sourceKPAdelicCutoffEisenstein K hζ T s q

theorem sourceKPAdelicInitialDifference_high {T : ℝ} (hT : 1 ≤ T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (hq : 2 * T ≤ sourceKPAdelicCoverHeight K hζ q) :
    sourceKPAdelicInitialDifference K hζ T s q =
      sourceKPAdelicNonconstantEisenstein K hζ s q + sourceKPAdelicTraceIntertwiner K hζ s q := by
  rw [sourceKPAdelicInitialDifference, sourceKPAdelicCutoffEisenstein_eq_of_high K hζ hT s q hq,
    sourceKPAdelicNonconstantEisenstein]
  ring

theorem sourceKPAdelicInitialDifference_high_norm_sq {T : ℝ} (hT : 1 ≤ T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (hq : 2 * T ≤ sourceKPAdelicCoverHeight K hζ q) :
    ‖sourceKPAdelicInitialDifference K hζ T s q‖ ^ 2 ≤
      2 * ‖sourceKPAdelicNonconstantEisenstein K hζ s q‖ ^ 2 +
        2 * ‖sourceKPAdelicTraceIntertwiner K hζ s q‖ ^ 2 := by
  rw [sourceKPAdelicInitialDifference_high K hζ hT s q hq]
  have hnorm := norm_add_le (sourceKPAdelicNonconstantEisenstein K hζ s q)
    (sourceKPAdelicTraceIntertwiner K hζ s q)
  have hsq := sq_nonneg (‖sourceKPAdelicNonconstantEisenstein K hζ s q‖ -
    ‖sourceKPAdelicTraceIntertwiner K hζ s q‖)
  nlinarith [norm_nonneg (sourceKPAdelicNonconstantEisenstein K hζ s q +
    sourceKPAdelicTraceIntertwiner K hζ s q), norm_nonneg (sourceKPAdelicNonconstantEisenstein K hζ s q),
    norm_nonneg (sourceKPAdelicTraceIntertwiner K hζ s q)]

end
end ArtinMatthews
