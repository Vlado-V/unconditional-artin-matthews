module

public import ArtinMatthews.SourceComplexTraceForm
public import ArtinMatthews.SourceArchimedeanRapid
public import Mathlib.Topology.Separation.CompletelyRegular


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def sourceComplexDualCoordinates (b : Module.Basis κ ℝ (ι → ℂ)) :
    (ι → ℂ) ≃L[ℝ] (κ → ℝ) :=
  OAI.RepresentationTheory.Weil.AdelicSplitting.LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates
    b sourceComplexTraceForm sourceComplexTraceForm_separating

/-- Shifted Poisson for the actual source probe, its trace Fourier transform
and its product self-dual measure. The Haar factor is kept explicit. -/
theorem sourceComplexProductTest_lattice_poisson_shift
    (b : Module.Basis κ ℝ (ι → ℂ)) (a : ι → ℂ) :
    (∑' n : κ → ℤ,
      sourceComplexProductFourier sourceComplexProductTest
        ((sourceComplexDualCoordinates b).symm (fun i => (n i : ℝ))) *
      OAI.RepresentationTheory.Weil.AdelicSplitting.RealCharacters.LocalAnalysis.realCharacter 1
        (sourceComplexTraceForm ((sourceComplexDualCoordinates b).symm (fun i => (n i : ℝ))) a)) =
      (OAI.RepresentationTheory.Weil.AdelicSplitting.LatticePoisson.LocalAnalysis.basisHaarFactor
        b (sourceComplexProductMeasure ι) : ℂ) *
          ∑' n : κ → ℤ, sourceComplexProductTest (a + b.equivFunL.symm (fun i => (n i : ℝ))) := by
  have hfg (x : ι → ℂ) : sourceComplexProductFourierRapid x =
      OAI.RepresentationTheory.Weil.AdelicSplitting.LatticePoisson.LocalAnalysis.realBilinearFourier
        sourceComplexTraceForm (sourceComplexProductMeasure ι) sourceComplexProductTestRapid x := by
    rw [sourceComplexProductFourierRapid_apply, sourceComplexProductFourier_eq_realBilinear]
    congr 1
  have h :=
    OAI.RepresentationTheory.Weil.AdelicSplitting.RapidLatticePoisson.LocalAnalysis.rapid_lattice_poisson_shift_positive
      b sourceComplexTraceForm (sourceComplexProductMeasure ι) sourceComplexTraceForm_separating
      sourceComplexProductTestRapid sourceComplexProductFourierRapid hfg a
  simpa only [sourceComplexProductFourierRapid_apply, sourceComplexProductTestRapid_apply,
    sourceComplexDualCoordinates] using h

theorem sourceComplexProductTest_lattice_haar_factor_pos
    (b : Module.Basis κ ℝ (ι → ℂ)) :
    0 < OAI.RepresentationTheory.Weil.AdelicSplitting.LatticePoisson.LocalAnalysis.basisHaarFactor
      b (sourceComplexProductMeasure ι) :=
  OAI.RepresentationTheory.Weil.AdelicSplitting.LatticePoisson.LocalAnalysis.basisHaarFactor_pos _ _

end
end ArtinMatthews.VaryingKummerAnalytic
