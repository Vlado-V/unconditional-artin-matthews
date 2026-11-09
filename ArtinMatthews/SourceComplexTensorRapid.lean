module

public import ArtinMatthews.SourceComplexIdealBasis


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped BigOperators SchwartzMap
noncomputable section
variable {ι : Type*} [Fintype ι]

def sourceComplexTensor (f : ι → 𝓢(ℂ, ℂ)) (x : ι → ℂ) : ℂ := ∏ i, f i (x i)

def sourceComplexTensorRapid (f : ι → 𝓢(ℂ, ℂ)) :
    RapidFunctions.LocalAnalysis.RapidFunction (ι → ℂ) :=
  RapidFunctions.LocalAnalysis.piRapidFunction
    (fun i => RapidFunctions.LocalAnalysis.schwartzRapidFunction (f i))

theorem sourceComplexTensorRapid_apply (f : ι → 𝓢(ℂ, ℂ)) (x : ι → ℂ) :
    sourceComplexTensorRapid f x = sourceComplexTensor f x := rfl

def sourceComplexTensorFourierRapid (f : ι → 𝓢(ℂ, ℂ)) :
    RapidFunctions.LocalAnalysis.RapidFunction (ι → ℂ) :=
  RapidFunctions.LocalAnalysis.piRapidFunction (fun i => sourceComplexTraceFourierRapid (f i))

theorem sourceComplexTensorFourierRapid_apply (f : ι → 𝓢(ℂ, ℂ)) (x : ι → ℂ) :
    sourceComplexTensorFourierRapid f x = sourceComplexProductFourier (sourceComplexTensor f) x := by
  change (∏ i, sourceComplexTraceFourier (f i) (x i)) = _
  exact (source_complex_product_fourier_tensor (fun i => f i) x).symm

theorem sourceRealCharacter_norm (t : ℝ) :
    ‖RealCharacters.LocalAnalysis.realCharacter 1 t‖ = 1 := by
  rw [RealCharacters.LocalAnalysis.realCharacter_apply, Complex.norm_exp]
  simp [Complex.mul_re]

end
end ArtinMatthews.VaryingKummerAnalytic
