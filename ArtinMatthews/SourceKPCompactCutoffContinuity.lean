module

public import ArtinMatthews.SourceKPAdelicCutoffContinuity
public import ArtinMatthews.SourceKPAutomorphicCompactCutoff
public import ArtinMatthews.SourceKPAutomorphicParametricContinuity


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAutomorphicCompactCutoffEisenstein_joint_continuous
    {T : ℝ} (hT : 0 < T) :
    Continuous (fun p : ℂ × SourceKPAutomorphicCompactLevel K hζ =>
      sourceKPAutomorphicCompactCutoffEisenstein K hζ T p.1 p.2) := by
  apply sourceKPAutomorphicCompactFamily_continuous_of_matrices K hζ
  intro qf
  simpa only [sourceKPAutomorphicCompactCutoffEisenstein_adelic] using
    sourceKPAdelicCutoffEisenstein_joint_matrix_continuous K hζ hT qf

end
end ArtinMatthews
