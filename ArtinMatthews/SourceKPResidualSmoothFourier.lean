module

public import ArtinMatthews.SourceKPResidualSmoothRepresentative
public import ArtinMatthews.SourceKPCuspWirtingerSeries
public import ArtinMatthews.SourceKPCuspTraceModeReindex
public import ArtinMatthews.SourceKPCuspResidualFourierValue
public import ArtinMatthews.SourceKPCuspResidualDualSupport
public import ArtinMatthews.SourceKPCuspResidualPointwiseFourier
public import ArtinMatthews.SourceKPCuspTraceModePhase
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

/-! The differentiated smooth residue is the series of the actual
canonical coefficients over all nonzero rational frequencies. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory SourceHyperbolicGreen UnitAddTorus IsDedekindDomain StandardAdelic
open scoped NumberField MatrixGroups AdeleRing Classical ContDiff nonZeroDivisors
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "V" => InfinitePlace K
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D[" d "]" => FractionalIdeal.dual ℤ ℚ
  ((Ideal.span ({d} : Set (𝓞 K)) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)

theorem sourceKPResidualSmooth_traceCellCoeff (d : 𝓞 K) (hd : d ≠ 0) (qf : Gf)
    (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf) {T : ℝ} (hT : 1 ≤ T)
    (n : I → ℤ) (hn : n ≠ 0) (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    let m := sourceKPCuspTraceModeUnit K d hd ⟨n,hn⟩
    sourceKPCuspNativeTraceCellCoeff K hζ d hd qf
        (sourceKPResidualSmoothRepresentative K hζ hT) n y =
      sourceKPCuspResidualFourierValue K hζ m hT qf *
        sourceKPTraceJacquetArchProfile K hζ m (1/6) y := by
  let m := sourceKPCuspTraceModeUnit K d hd ⟨n,hn⟩
  let W := sourceKPResidualSmoothRepresentative K hζ hT
  let U := sourceKPCompactChartPullback K hζ W (QuotientGroup.mk qf)
  have hm : (m : K) ∈ D[d] := sourceKPCuspTraceFrequency_mem_dual K d n
  have hU := sourceKPResidualSmoothRepresentative_chart K hζ hT (QuotientGroup.mk qf)
  have hUae := sourceKPResidualSmoothRepresentative_chart_ae K hζ hT (QuotientGroup.mk qf)
  change sourceKPCuspNativeTraceCellCoeff K hζ d hd qf W n y = _
  rw [← sourceKPCuspRepresentativeFourierCell_eq_value_of_dual K hζ d hd qf hperiod
    m hm hT U hU.continuousOn hUae y hy]
  unfold sourceKPCuspNativeTraceCellCoeff sourceKPCuspRepresentativeFourierCell
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    let p := sourceKPCuspProductCoordinates K hζ d hd (x,y)
    have hp : p ∈ productUpper V := by
      intro v _
      change 0 < sourceKPCuspProductCoordinates K hζ d hd (x,y) v 2
      simpa only [sourceKPCuspProductCoordinates_height] using hy v
    have hU : U p = W (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf) p) := by
      unfold U sourceKPCompactChartPullback sourceKPCompactCoordinateProjection
      rw [if_pos hp]
    change mFourier (-n) (unitTorusUnitCellProjection I x) •
      W (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf) p) =
      star (character K (algebraMap K 𝔸[K] (m : K) * sourceKPCuspUnitCellAdelicPoint K d hd x)) *
        U p
    rw [← hU,show (m : K) = sourceKPCuspTraceFrequency K d n from rfl,
      sourceKPCuspTraceFrequency_unitCell_star_phase K d hd n x, smul_eq_mul]

theorem sourceKPResidualSmooth_horizontal_hasSum (qf : Gf) {T : ℝ} (hT : 1 ≤ T)
    (ε : V → Bool) (l : List V) (hl : l ≠ []) (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    HasSum (fun m : Kˣ =>
      sourceKPCuspWirtingerProductFrequency K ε l (m : K) y *
        (sourceKPCuspResidualFourierValue K hζ m hT qf *
          sourceKPTraceJacquetArchProfile K hζ m (1/6) y))
      (sourceProductHorizontalList ε l
        (sourceKPCompactChartPullback K hζ (sourceKPResidualSmoothRepresentative K hζ hT)
          (QuotientGroup.mk qf)) (sourceKPCuspHeightPoint K y)) := by
  obtain ⟨d,hd,hperiod⟩ :=
    sourceKPAdelicCuspFiniteLevelPeriod K hζ ((1,qf) : SourceKPAdelicProjective K hζ)
  let W := sourceKPResidualSmoothRepresentative K hζ hT
  let a := sourceProductHorizontalList ε l
    (sourceKPCompactChartPullback K hζ W (QuotientGroup.mk qf)) (sourceKPCuspHeightPoint K y)
  let f (m : Kˣ) := sourceKPCuspWirtingerProductFrequency K ε l (m : K) y *
    (sourceKPCuspResidualFourierValue K hζ m hT qf *
      sourceKPTraceJacquetArchProfile K hζ m (1/6) y)
  let g (n : I → ℤ) := sourceKPCuspWirtingerProductFrequency K ε l
    (sourceKPCuspTraceFrequency K d n) y * sourceKPCuspNativeTraceCellCoeff K hζ d hd qf W n y
  have hg : HasSum g a := sourceKPCuspNativeHorizontal_hasSum K hζ d hd qf hperiod W
    (sourceKPResidualSmoothRepresentative_chart K hζ hT (QuotientGroup.mk qf)) ε l y hy
  have hg0 : g 0 = 0 := by
    have h := (sourceKPCuspTraceFrequency_zero_iff K d hd 0).2 rfl
    simp only [g,h,sourceKPCuspWirtingerProductFrequency_zero K ε l hl y,zero_mul]
  have hgs : Function.support g ⊆ {n | n ≠ 0} := by
    intro n hn h
    exact (Function.mem_support.mp hn) (h.symm ▸ hg0)
  have hf0 (m : Kˣ) (hm : (m : K) ∉ D[d]) : f m = 0 := by
    simp only [f,sourceKPCuspResidualFourierValue_eq_zero_of_not_mem_dual
      K hζ d hd qf hperiod m hT hm,zero_mul,mul_zero]
  change HasSum f a
  apply (sourceKPCuspTraceModeUnit_hasSum_iff K d hd f hf0 a).mp
  have hh := (hasSum_subtype_iff_of_support_subset hgs).mpr hg
  apply hh.congr_fun
  intro n
  change f (sourceKPCuspTraceModeUnit K d hd n) = g n.val
  unfold f g
  rw [sourceKPResidualSmooth_traceCellCoeff K hζ d hd qf hperiod hT n.val n.property y hy]
  rfl

end
end ArtinMatthews
