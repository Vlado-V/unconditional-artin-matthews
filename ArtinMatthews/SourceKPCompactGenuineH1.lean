module

public import ArtinMatthews.SourceKPCompactH1Completion
public import ArtinMatthews.SourceKPCompactGenuineL2


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine subspace of the actual completed compact-quotient form. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "V" => SourceKPCompactH1 K hζ
local notation "L" => SourceKPAutomorphicL2 K hζ (sourceKPArchHaar K hζ)
local notation "G" => sourceKPCompactGenuineL2Subspace K hζ (sourceKPArchHaar K hζ)

def sourceKPCompactGenuineH1 : Submodule ℂ V :=
  (G).comap (sourceKPCompactH1Mass K hζ).toLinearMap

abbrev SourceKPCompactGenuineH1 := ↥(sourceKPCompactGenuineH1 K hζ)

theorem sourceKPCompactGenuineH1_isClosed :
    IsClosed (sourceKPCompactGenuineH1 K hζ : Set V) :=
  (sourceKPCompactGenuineL2Subspace_isClosed K hζ (sourceKPArchHaar K hζ)).preimage
    (sourceKPCompactH1Mass K hζ).continuous

instance sourceKPCompactGenuineH1_complete : CompleteSpace (SourceKPCompactGenuineH1 K hζ) :=
  (sourceKPCompactGenuineH1_isClosed K hζ).completeSpace_coe

def sourceKPCompactGenuineH1Mass :
    SourceKPCompactGenuineH1 K hζ →L[ℂ] SourceKPGenuineAutomorphicL2 K hζ :=
  ((sourceKPCompactH1Mass K hζ).comp (sourceKPCompactGenuineH1 K hζ).subtypeL).codRestrict
    G (fun u => u.prop)

theorem sourceKPCompactGenuineH1Mass_coe (u : SourceKPCompactGenuineH1 K hζ) :
    (sourceKPCompactGenuineH1Mass K hζ u : L) = sourceKPCompactH1Mass K hζ u.val :=
  rfl

theorem sourceKPCompactGenuineH1Mass_norm_le (u : SourceKPCompactGenuineH1 K hζ) :
    ‖sourceKPCompactGenuineH1Mass K hζ u‖ ≤ ‖u‖ :=
  sourceKPCompactH1Mass_norm_le K hζ u.val

theorem sourceKPCompactGenuineH1Dirichlet_self (u : SourceKPCompactGenuineH1 K hζ) :
    (sourceKPCompactH1Dirichlet K hζ u.val u.val).re =
      ‖u‖ ^ 2 - ‖sourceKPCompactGenuineH1Mass K hζ u‖ ^ 2 :=
  sourceKPCompactH1Dirichlet_self K hζ u.val

end
end ArtinMatthews
