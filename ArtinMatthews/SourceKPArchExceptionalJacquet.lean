module

public import ArtinMatthews.SourceKPArchJacquetDiagonal
public import ArtinMatthews.SourceKPTraceJacquetArchProduct
public import ArtinMatthews.SourceArchActualVector
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

/-! The unit-frequency archimedean Jacquet factor at the exceptional parameter
is the literal product of normalized local Bessel profiles. -/
namespace ArtinMatthews
open NumberField MeasureTheory Matrix StandardAdelic SourceArchJacquet
open OAI.RepresentationTheory.Weil
open scoped NumberField AdeleRing MatrixGroups BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceArchExceptionalJacquetCompletionMeasurable (v : InfinitePlace K) :
    MeasurableSpace v.Completion := borel _
local instance sourceArchExceptionalJacquetCompletionBorel (v : InfinitePlace K) :
    BorelSpace v.Completion := ⟨rfl⟩
local instance sourceArchExceptionalJacquetInfiniteMeasurable : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ v : InfinitePlace K, v.Completion))

theorem sourceKPTraceJacquetLocalArchKernel_one_diagonal
    (y : (v : InfinitePlace K) → v.Completionˣ) (v : InfinitePlace K)
    (hv : InfinitePlace.IsComplex v) (x : v.Completion) :
    sourceKPTraceJacquetLocalArchKernel K hζ 1 (1/6) (sourceKPArchJacquetDiagonal K y) v x =
      sourceArchCompletedSphericalSection K v hv (1/6)
        (sourcePGL2Weyl * sourcePGL2Upper x * sourcePGL2Diagonal (y v)) *
        localInfiniteCharacter K v (-x) := by
  unfold sourceKPTraceJacquetLocalArchKernel
  rw [Units.val_one,map_one,one_mul,sourceKPLocalInfiniteCharacter_star,
    sourceKPArchJacquetDiagonal_localSection K hζ (1/6) y v hv]
  exact mul_comm _ _

theorem sourceKPTraceJacquetArch_one_diagonal_eq_whittaker
    (hc : ∀ v : InfinitePlace K, InfinitePlace.IsComplex v)
    (y : (v : InfinitePlace K) → v.Completionˣ) :
    (∫ x, sourceKPTraceJacquetArchKernel K hζ 1 (1/6) (sourceKPArchJacquetDiagonal K y) x
      ∂sourceKPArchSelfDualProduct K) =
      ∏ v : InfinitePlace K, sourceArchCompletedWhittaker K v (hc v) (y v) := by
  rw [(sourceKPTraceJacquetArchKernel_integral_product K hζ
    (s := 1/6) (by norm_num) 1 (sourceKPArchJacquetDiagonal K y)).2]
  apply Finset.prod_congr rfl
  intro v _
  unfold sourceArchCompletedWhittaker
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (sourceKPTraceJacquetLocalArchKernel_one_diagonal K hζ y v (hc v))

theorem sourceKPTraceJacquetArch_one_diagonal_bessel
    (y : (v : InfinitePlace K) → v.Completionˣ) :
    (∫ x, sourceKPTraceJacquetArchKernel K hζ 1 (1/6) (sourceKPArchJacquetDiagonal K y) x
      ∂sourceKPArchSelfDualProduct K) =
      ∏ v : InfinitePlace K, (sourceArchJacquetConstant*‖(y v : v.Completion)‖ : ℝ) *
        OAI.CubicEisenstein.schlafliBesselK (1/3 : ℂ) (4*Real.pi*‖(y v : v.Completion)‖) := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  rw [sourceKPTraceJacquetArch_one_diagonal_eq_whittaker K hζ (fun v => IsTotallyComplex.isComplex v) y]
  simp_rw [sourceArchCompletedWhittaker_bessel]

theorem sourceKPTraceJacquetArch_one_diagonal_ne_zero
    (y : (v : InfinitePlace K) → v.Completionˣ) :
    (∫ x, sourceKPTraceJacquetArchKernel K hζ 1 (1/6) (sourceKPArchJacquetDiagonal K y) x
      ∂sourceKPArchSelfDualProduct K) ≠ 0 := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  rw [sourceKPTraceJacquetArch_one_diagonal_eq_whittaker K hζ (fun v => IsTotallyComplex.isComplex v) y]
  exact Finset.prod_ne_zero_iff.mpr
    (fun v _ => sourceArchCompletedWhittaker_ne_zero K v (IsTotallyComplex.isComplex v) (y v))

end
end ArtinMatthews
