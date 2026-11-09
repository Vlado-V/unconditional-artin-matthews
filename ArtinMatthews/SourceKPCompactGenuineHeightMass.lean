module

public import ArtinMatthews.SourceKPCompactGenuineH1
public import ArtinMatthews.SourceKPCompactHeightMass


set_option backward.privateInPublic true
@[expose] public section

/-! The same literal sublevel restriction on the actual genuine form space. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "Vχ" => SourceKPCompactGenuineH1 K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "L" => Lp ℂ 2 μ
local notation "S" => (fun R : ℝ => Set.ofPred (fun y : Y => sourceKPAutomorphicCompactOrbitHeight K hζ y ≤ R))

def sourceKPCompactGenuineH1LocalizedMass (R : ℝ) : Vχ →L[ℂ] L :=
  (sourceKPCompactH1LocalizedMass K hζ R).comp (sourceKPCompactGenuineH1 K hζ).subtypeL

theorem sourceKPCompactGenuineH1LocalizedMass_apply (R : ℝ) (u : Vχ) :
    sourceKPCompactGenuineH1LocalizedMass K hζ R u =
      sourceKPCompactHeightCutoff K hζ R (sourceKPCompactGenuineH1Mass K hζ u : L) :=
  rfl

theorem sourceKPCompactGenuineH1LocalizedMass_coe (R : ℝ) (u : Vχ) :
    (sourceKPCompactGenuineH1LocalizedMass K hζ R u : Y → ℂ) =ᵐ[μ]
      (S R).indicator (sourceKPCompactGenuineH1Mass K hζ u : L) :=
  sourceKPCompactH1LocalizedMass_coe K hζ R u.val

theorem sourceKPCompactGenuineH1LocalizedMass_norm_sq (R : ℝ) (u : Vχ) :
    ‖sourceKPCompactGenuineH1LocalizedMass K hζ R u‖ ^ 2 =
      ∫ y in S R, ‖(sourceKPCompactGenuineH1Mass K hζ u : L) y‖ ^ 2 ∂μ :=
  sourceKPCompactH1LocalizedMass_norm_sq K hζ R u.val

end
end ArtinMatthews
