module

public import ArtinMatthews.SourceKPCuspNativeTraceSlice
public import ArtinMatthews.SourceKPCompactC2Core
public import ArtinMatthews.UnitTorusSmoothFourier
public import ArtinMatthews.VaryingKummerAnalyticPoisson
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

/-! The literal principal horizontal slice has a smooth periodic lift
through the actual affine product chart. Its Fourier coefficients use
the original normalized Haar measure and unit cell. -/

namespace ArtinMatthews

open NumberField Module.Free MeasureTheory SourceHyperbolicGreen UnitAddTorus
open scoped NumberField AdeleRing ContDiff Classical

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (d : 𝓞 K) (hd : d ≠ 0)
    (qf : SourceKPFiniteAdeleProjective K hζ)
    (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf)

local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K

private theorem sourceKPCuspProductCoordinates_mem_upper (x : I → ℝ) (y : V → ℝ)
    (hy : ∀ v, 0 < y v) :
    sourceKPCuspProductCoordinates K hζ d hd (x,y) ∈ productUpper V := by
  intro v _
  change 0 < sourceKPCuspProductCoordinates K hζ d hd (x,y) v 2
  simpa only [sourceKPCuspProductCoordinates_height] using hy v

theorem sourceKPCuspNativeTraceSlice_lift_eq_chart
    (W : SourceKPAutomorphicCompactLevel K hζ → ℂ) (y : V → ℝ) (hy : ∀ v, 0 < y v)
    (x : I → ℝ) :
    sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy (unitTorusUnitCellProjection I x) =
      sourceKPCompactChartPullback K hζ W (QuotientGroup.mk qf)
        (sourceKPCuspProductCoordinates K hζ d hd (x,y)) := by
  rw [sourceKPCuspNativeTraceSlice_unitCell]
  unfold sourceKPCompactChartPullback sourceKPCompactCoordinateProjection
  exact (ite_eq_left (sourceKPCuspProductCoordinates_mem_upper K hζ d hd x y hy)).symm

theorem sourceKPCuspNativeTraceSlice_lift_integer_periodic
    (W : SourceKPAutomorphicCompactLevel K hζ → ℂ) (y : V → ℝ) (hy : ∀ v, 0 < y v) (k : I → ℤ) :
    Function.Periodic
      (fun x : I → ℝ => sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy
        (unitTorusUnitCellProjection I x)) (fun i => (k i : ℝ)) := by
  intro x
  exact congrArg (sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy)
    (ReusedTheta.torusProjection_add_integer x k)

theorem sourceKPCuspNativeTraceSlice_lift_contDiff
    (W : SourceKPAutomorphicCompactLevel K hζ → ℂ)
    (hW : ContDiffOn ℝ (∞ : ℕ∞ω)
      (sourceKPCompactChartPullback K hζ W (QuotientGroup.mk qf)) (productUpper (InfinitePlace K)))
    (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v) :
    ContDiff ℝ (∞ : ℕ∞ω) (fun x : I → ℝ => sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy
      (unitTorusUnitCellProjection I x)) := by
  have hc : ContDiff ℝ (∞ : ℕ∞ω) (fun x : I → ℝ => sourceKPCuspProductCoordinates K hζ d hd (x,y)) :=
    (sourceKPCuspProductCoordinates K hζ d hd).contDiff.comp (contDiff_id.prodMk contDiff_const)
  apply contDiffOn_univ.mp
  refine (hW.comp hc.contDiffOn (fun x _ => sourceKPCuspProductCoordinates_mem_upper K hζ d hd x y hy)).congr ?_
  intro x _
  exact sourceKPCuspNativeTraceSlice_lift_eq_chart K hζ d hd qf hperiod W y hy x

theorem sourceKPCuspNativeTraceSlice_continuous
    (W : SourceKPAutomorphicCompactLevel K hζ → ℂ)
    (hW : ContDiffOn ℝ (∞ : ℕ∞ω)
      (sourceKPCompactChartPullback K hζ W (QuotientGroup.mk qf)) (productUpper (InfinitePlace K)))
    (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v) :
    Continuous (sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy) :=
  (ReusedTheta.torusProjection_openQuotient (d := I)).isQuotientMap.continuous_iff.mpr
    (sourceKPCuspNativeTraceSlice_lift_contDiff K hζ d hd qf hperiod W hW y hy).continuous

theorem sourceKPCuspNativeTraceSlice_summable_norm_fourierCoeff
    (W : SourceKPAutomorphicCompactLevel K hζ → ℂ)
    (hW : ContDiffOn ℝ (∞ : ℕ∞ω)
      (sourceKPCompactChartPullback K hζ W (QuotientGroup.mk qf)) (productUpper (InfinitePlace K)))
    (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v) :
    Summable (fun n : I → ℤ =>
      ‖mFourierCoeff (sourceKPCuspNativeTraceSlice K hζ d hd qf hperiod W y hy) n‖) :=
  unitTorus_summable_norm_mFourierCoeff_of_smooth I _
    (sourceKPCuspNativeTraceSlice_continuous K hζ d hd qf hperiod W hW y hy)
    (sourceKPCuspNativeTraceSlice_lift_contDiff K hζ d hd qf hperiod W hW y hy)

include hperiod in
theorem sourceKPCuspNativeTraceCellCoeff_summable_norm
    (W : SourceKPAutomorphicCompactLevel K hζ → ℂ)
    (hW : ContDiffOn ℝ (∞ : ℕ∞ω)
      (sourceKPCompactChartPullback K hζ W (QuotientGroup.mk qf)) (productUpper (InfinitePlace K)))
    (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v) :
    Summable (fun n : I → ℤ => ‖sourceKPCuspNativeTraceCellCoeff K hζ d hd qf W n y‖) := by
  have hs := sourceKPCuspNativeTraceSlice_summable_norm_fourierCoeff K hζ d hd qf hperiod W hW y hy
  simpa only [sourceKPCuspNativeTraceSlice_fourierCoeff] using hs

end
end ArtinMatthews
