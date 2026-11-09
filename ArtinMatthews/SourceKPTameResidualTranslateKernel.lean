module

public import ArtinMatthews.SourceKPResidualTranslateKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The constant-term relation for an actual negative cyclic vector descends
through the closed-form nullspace to the actual finite-level translate. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical
open scoped NumberField MatrixGroups AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (F : Finset (SourceKPFiniteAdeleProjective K hζ))
variable {ι : Type*} [Fintype ι] (c : ι → ℂ) {T : ℝ} (hT : 2 < T)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P.val

/-- The genuine common-level residual representation kills the actual
whole-section negative cyclic relations. -/
theorem sourceKPResidualTranslateCombination_eq_zero_of_negativeCyclicRelation
    (hP : P.val ∉ traceBadPlaces K) (g : ι → SourceFiniteKP2Projective K hζ P.val)
    (hg : ∀ i, sourceKPFiniteTranslateLevel K hζ F ≤
      sourceKPFiniteLevelConjugate K hζ (ι₀ (g i)).2)
    (hrel : SourceKPLocalNegativeCyclicRelation K hζ S₀ P g c) :
    sourceKPResidualTranslateCombination K hζ F (fun i => (ι₀ (g i)).2) hg c hT = 0 :=
  sourceKPResidualTranslateCombination_eq_zero_of_archMean_zero K hζ F
    (fun i => (ι₀ (g i)).2) hg c hT
    (fun qf => sourceKPResidualTraceOrbit_cyclic_combination_ae K hζ S₀ P hP qf g c hrel
      (by linarith : 1 ≤ T))

end
end ArtinMatthews
