module

public import ArtinMatthews.SourceKPArchJacquetDiagonal
public import ArtinMatthews.SourceKPTraceJacquetArchProduct


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
