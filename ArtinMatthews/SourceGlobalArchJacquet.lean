module

public import ArtinMatthews.SourceArchCompletedJacquet
public import ArtinMatthews.SourceKPAdelicCompactSection
public import ArtinMatthews.SourceSLocalOtherTensor
public import ArtinMatthews.SourceArchActualVector
public import ArtinMatthews.SourceGlobalArchLocalValue
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


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix MeasureTheory
open SourceArchJacquet OAI.RepresentationTheory.Weil
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local instance globalArchMeasurable (v : InfinitePlace K) : MeasurableSpace v.Completion :=
  borel v.Completion
local instance globalArchBorel (v : InfinitePlace K) : BorelSpace v.Completion := ⟨rfl⟩

def sourceGlobalArchJacquet (v : InfinitePlace K) (y : v.Completionˣ)
    (qf : SourceKPFiniteAdeleProjective K hζ) : ℂ :=
  ∫ x : v.Completion, sourceKPAdelicCompactScalar K hζ (1/6)
      (sourceArchSinglePGL K v (sourcePGL2Weyl * sourcePGL2Upper x * sourcePGL2Diagonal y),qf) *
      StandardAdelic.localInfiniteCharacter K v (-x)
    ∂Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion
      (StandardAdelic.localInfiniteCharacter K v)

theorem sourceGlobalArchJacquet_integrable (v : InfinitePlace K)
    (hv : InfinitePlace.IsComplex v) (y : v.Completionˣ)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    Integrable (fun x : v.Completion => sourceKPAdelicCompactScalar K hζ (1/6)
      (sourceArchSinglePGL K v (sourcePGL2Weyl * sourcePGL2Upper x * sourcePGL2Diagonal y),qf) *
        StandardAdelic.localInfiniteCharacter K v (-x))
      (Local.FunctionsMetaplectic.Construction.selfDualMeasure v.Completion
        (StandardAdelic.localInfiniteCharacter K v)) := by
  refine ((sourceArchCompletedWhittaker_integrable K v hv y).mul_const
    (sourceKPAdelicCompactScalar K hζ (1/6) (1,qf))).congr (Filter.Eventually.of_forall ?_)
  intro x
  dsimp only
  rw [sourceGlobalArchLocal_scalar K hζ (1/6) v hv]
  ring

theorem sourceGlobalArchJacquet_eq (v : InfinitePlace K)
    (hv : InfinitePlace.IsComplex v) (y : v.Completionˣ)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    sourceGlobalArchJacquet K hζ v y qf = sourceArchCompletedWhittaker K v hv y *
      sourceKPAdelicCompactScalar K hζ (1/6) (1,qf) := by
  unfold sourceGlobalArchJacquet sourceArchCompletedWhittaker
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with x
  rw [sourceGlobalArchLocal_scalar K hζ (1/6) v hv]
  ring

theorem sourceGlobalArchJacquet_bessel (v : InfinitePlace K)
    (hv : InfinitePlace.IsComplex v) (y : v.Completionˣ)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    sourceGlobalArchJacquet K hζ v y qf =
      (sourceArchJacquetConstant * ‖(y : v.Completion)‖ : ℝ) *
        OAI.CubicEisenstein.schlafliBesselK (1/3 : ℂ) (4*Real.pi*‖(y : v.Completion)‖) *
        sourceKPAdelicCompactScalar K hζ (1/6) (1,qf) := by
  rw [sourceGlobalArchJacquet_eq K hζ v hv, sourceArchCompletedWhittaker_bessel K v hv]

theorem sourceGlobalArchJacquet_one (v : InfinitePlace K)
    (hv : InfinitePlace.IsComplex v) (y : v.Completionˣ) :
    sourceGlobalArchJacquet K hζ v y 1 = sourceArchCompletedWhittaker K v hv y := by
  rw [sourceGlobalArchJacquet_eq K hζ v hv]
  change _ * sourceKPAdelicCompactScalar K hζ (1/6) 1 = _
  rw [sourceKPAdelicCompactScalar_one, mul_one]

theorem sourceGlobalArchJacquet_one_ne_zero (v : InfinitePlace K)
    (hv : InfinitePlace.IsComplex v) (y : v.Completionˣ) :
    sourceGlobalArchJacquet K hζ v y 1 ≠ 0 := by
  rw [sourceGlobalArchJacquet_one K hζ v hv]
  exact sourceArchCompletedWhittaker_ne_zero K v hv y

theorem sourceGlobalArchJacquet_sheet_weight (v : InfinitePlace K)
    (hv : InfinitePlace.IsComplex v) (y : v.Completionˣ)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    SourceReflection.sourceThetaBesselProfile (4*Real.pi) (SourcePhysical.sourceSheetArchNorm v y) *
        sourceKPAdelicCompactScalar K hζ (1/6) (1,qf) =
      (Real.sqrt (SourcePhysical.sourceSheetArchNorm v y) : ℂ) *
        sourceGlobalArchJacquet K hζ v y qf / (sourceArchJacquetConstant : ℂ) := by
  rw [sourceArchCompletedWhittaker_sourceNorm K v hv, sourceGlobalArchJacquet_eq K hζ v hv]
  ring

end
end ArtinMatthews
