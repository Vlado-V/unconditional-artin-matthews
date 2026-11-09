module

public import ArtinMatthews.SourceKPCompactC2Core
public import ArtinMatthews.SourceKPAutomorphicCompactHaar


set_option backward.privateInPublic true
@[expose] public section

/-! Compact scalar tests have genuine mass in the canonical Haar L2 space. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCompactCore_memLp {n : ℕ∞ω} (f : sourceKPCompactCore K hζ n) :
    MemLp f.val 2 (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) := by
  let : IsFiniteMeasureOnCompacts
      (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) :=
    sourceKPAutomorphicCompactHaar_finiteOnCompacts K hζ
  exact f.prop.1.memLp_of_hasCompactSupport f.prop.2.1

def sourceKPCompactCoreMass (n : ℕ∞ω) : sourceKPCompactCore K hζ n →ₗ[ℂ]
    Lp ℂ 2 (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) where
  toFun f := (sourceKPCompactCore_memLp K hζ f).toLp f.val
  map_add' _f _g := MemLp.toLp_add _ _
  map_smul' c _f := MemLp.toLp_const_smul c _

theorem sourceKPCompactCoreMass_coe {n : ℕ∞ω} (f : sourceKPCompactCore K hζ n) :
    (sourceKPCompactCoreMass K hζ n f : SourceKPAutomorphicCompactLevel K hζ → ℂ) =ᵐ[
      sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)] f.val :=
  (sourceKPCompactCore_memLp K hζ f).coeFn_toLp

end
end ArtinMatthews
