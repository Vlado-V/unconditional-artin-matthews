module

public import ArtinMatthews.SourceKPCubicCompactAction
public import ArtinMatthews.SourceKPCompactCoreCharts


set_option backward.privateInPublic true
@[expose] public section

/-! The actual cubic center permutes upper-half-space components with fixed coordinates. -/
namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCubicCenter_upperToCompact (z : rootsOfUnity 3 K)
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    z • sourceKPUpperToCompact K hζ b p = sourceKPUpperToCompact K hζ (z • b) p := by
  obtain ⟨a, ha⟩ := Quotient.mk_surjective ((sourceKPArchSymmetricHomeomorph K hζ).symm p)
  have hp : sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a) = p :=
    (congrArg (sourceKPArchSymmetricHomeomorph K hζ) ha).trans
      ((sourceKPArchSymmetricHomeomorph K hζ).apply_symm_apply p)
  rw [← hp]
  change z • (sourceKPArithmeticUpperComponentHomeomorph K hζ b
      (Quotient.mk _ (sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a))) :
      SourceKPAutomorphicCompactLevel K hζ) =
    (sourceKPArithmeticUpperComponentHomeomorph K hζ (z • b)
      (Quotient.mk _ (sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a))) :
      SourceKPAutomorphicCompactLevel K hζ)
  rw [sourceKPArithmeticUpperComponentHomeomorph_mk,
    sourceKPArithmeticUpperComponentHomeomorph_mk, sourceKPCubicCenter_compact_mk,
    sourceKPCubicCenter_component_point]

def sourceKPCubicCenterCompactHomeomorph (z : rootsOfUnity 3 K) :
    SourceKPAutomorphicCompactLevel K hζ ≃ₜ SourceKPAutomorphicCompactLevel K hζ :=
  Homeomorph.smul z

@[simp] theorem sourceKPCubicCenterCompactHomeomorph_apply (z : rootsOfUnity 3 K)
    (x : SourceKPAutomorphicCompactLevel K hζ) :
    sourceKPCubicCenterCompactHomeomorph K hζ z x = z • x := rfl

end
end ArtinMatthews
