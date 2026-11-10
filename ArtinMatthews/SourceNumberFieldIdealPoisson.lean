module

public import ArtinMatthews.SourceComplexTensorRapid
public import ArtinMatthews.SourceComplexAdelicCharacter
public import ArtinMatthews.SourceComplexIdealBasis
public import ArtinMatthews.SourceComplexIdealCovolume
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
open MeasureTheory Module NumberField NumberField.InfinitePlace
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField nonZeroDivisors Classical BigOperators SchwartzMap
noncomputable section
variable (K : Type) [Field K] [NumberField K]
local notation "CPlaces" => {v : InfinitePlace K // IsComplex v}

theorem sourceComplexTraceForm_positive_character (x y : CPlaces → ℂ) :
    StandardAdelic.archCharacter K (sourceComplexPlaceAdele K x * sourceComplexPlaceAdele K y) =
      RealCharacters.LocalAnalysis.realCharacter 1 (sourceComplexTraceForm x y) := by
  change Complex.exp ((StandardAdelic.archTrace K
    (sourceComplexPlaceAdele K x * sourceComplexPlaceAdele K y) : ℂ) * _) = _
  rw [sourceComplexPlaceAdele_trace_mul, sourceComplexTraceForm_apply,
    RealCharacters.LocalAnalysis.realCharacter_apply, mul_one]
  congr 1
  push_cast
  ring

variable [IsTotallyComplex K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- Shifted Poisson on the actual nonzero fractional ideal and its complete
trace-dual ideal, using the original adelic archimedean character and measure. -/
theorem sourceNumberFieldIdealPoisson (f : CPlaces → 𝓢(ℂ, ℂ)) (a : CPlaces → ℂ) :
    (∑' z : (mixedTraceDualIdeal K I).1,
      sourceNumberFieldComplexFourier K (sourceComplexTensor f) (sourceComplexFieldEmbedding K (z : K)) *
        StandardAdelic.archCharacter K
          (sourceComplexPlaceAdele K (sourceComplexFieldEmbedding K (z : K)) * sourceComplexPlaceAdele K a)) =
      (((FractionalIdeal.absNorm I.1 : ℝ) * Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
        ∑' z : I.1, sourceComplexTensor f (a + sourceComplexFieldEmbedding K (z : K)) := by
  simp_rw [sourceNumberFieldComplexFourier_eq, sourceComplexTraceForm_positive_character]
  let b := sourceIdealComplexBasis K I
  have hfg (y : CPlaces → ℂ) : sourceComplexTensorFourierRapid f y =
      LatticePoisson.LocalAnalysis.realBilinearFourier sourceComplexTraceForm
        (sourceComplexProductMeasure CPlaces) (sourceComplexTensorRapid f) y := by
    rw [sourceComplexTensorFourierRapid_apply, sourceComplexProductFourier_eq_realBilinear]
    congr 1
  have h := RapidLatticePoisson.LocalAnalysis.rapid_lattice_poisson_shift_positive
    b sourceComplexTraceForm (sourceComplexProductMeasure CPlaces) sourceComplexTraceForm_separating
    (sourceComplexTensorRapid f) (sourceComplexTensorFourierRapid f) hfg a
  have hd : LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b sourceComplexTraceForm
      sourceComplexTraceForm_separating = sourceComplexDualCoordinates (sourceIdealComplexBasis K I) := rfl
  have hc : (LatticePoisson.LocalAnalysis.basisHaarFactor b (sourceComplexProductMeasure CPlaces) : ℂ) =
      (((FractionalIdeal.absNorm I.1 : ℝ) * Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) :=
    congrArg Complex.ofReal (sourceIdealComplexBasis_haar_factor K I)
  simp_rw [sourceComplexTensorFourierRapid_apply, sourceComplexTensorRapid_apply,
    hd, sourceIdealComplexBasis_dual_integer, hc, b, sourceIdealComplexBasis_integer] at h
  rw [(mixedDualIntegerEquiv K I).tsum_eq (fun z : (mixedTraceDualIdeal K I).1 =>
      sourceComplexProductFourier (sourceComplexTensor f) (sourceComplexFieldEmbedding K (z : K)) *
        RealCharacters.LocalAnalysis.realCharacter 1 (sourceComplexTraceForm (sourceComplexFieldEmbedding K (z : K)) a))] at h
  have hp : (∑' n : MixedIdealIndex K I → ℤ, sourceComplexTensor f
      (a + sourceComplexFieldEmbedding K (((fractionalIdealBasis K I.1).equivFun.symm n : I.1) : K))) =
      ∑' z : I.1, sourceComplexTensor f (a + sourceComplexFieldEmbedding K (z : K)) :=
    ((fractionalIdealBasis K I.1).equivFun.symm.toEquiv).tsum_eq
      (fun z : I.1 => sourceComplexTensor f (a + sourceComplexFieldEmbedding K (z : K)))
  rw [hp] at h
  exact h

end
end ArtinMatthews.VaryingKummerAnalytic
