module

public import ArtinMatthews.SourceComplexTraceForm
public import Mathlib.Topology.Separation.CompletelyRegular
public import ArtinMatthews.SourceArchimedeanRapid
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import OAI.RepresentationTheory.Weil.AdelicSplitting.RapidLatticePoisson


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
