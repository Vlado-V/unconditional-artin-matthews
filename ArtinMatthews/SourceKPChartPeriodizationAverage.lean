module

public import ArtinMatthews.SourceKPChartPeriodizationCore
public import ArtinMatthews.SourceKPFiniteChartAverage
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

/-! In a selected chart, arithmetic periodization is the exact finite stabilizer sum. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)

theorem sourceKPChartPeriodizationCore_support (φ : SourceKPFiniteChartTests K hζ b p) :
    tsupport (sourceKPChartPeriodizationCore K hζ b φ.val).val ⊆
      Set.range (sourceKPFiniteChartProjection K hζ b p) := by
  intro y hy
  obtain ⟨x,⟨z,hz,hzx⟩,rfl⟩ :=
    sourceKPChartPeriodizationGlobal_tsupport K hζ b φ.val hy
  obtain ⟨w,hw,hwz⟩ := φ.prop hz
  have he : x = w := hzx.symm.trans
    ((congrArg (sourceKPArchEuclideanUpperMap K) hwz.symm).trans
      (sourceKPArchUpperEuclideanMap_left_inverse K w))
  exact ⟨⟨w,hw⟩, congrArg (sourceKPUpperToCompact K hζ b) he.symm⟩

theorem sourceKPChartPeriodizationCore_local_sum (φ : SourceKPFiniteChartTests K hζ b p)
    (x : (sourceKPUpperFiniteChart K hζ b p).domain) :
    (sourceKPChartPeriodizationCore K hζ b φ.val).val (sourceKPFiniteChartProjection K hζ b p x) =
      ∑ γ : SourceKPFiniteChartStabilizer K hζ b p,
        φ.val.val (sourceKPArchUpperEuclideanMap K (γ.val • x.val)) := by
  change sourceKPChartPeriodizationGlobal K hζ b φ.val (sourceKPUpperToCompact K hζ b x.val) = _
  rw [sourceKPChartPeriodizationGlobal_apply]
  unfold sourceKPChartPeriodization
  have hs : Function.support (fun γ => sourceKPChartPeriodTerm K hζ b φ.val γ x.val) ⊆
      (SourceKPFiniteChartStabilizer K hζ b p : Set (sourceKPArchComponentSubgroup K hζ b)) := by
    intro γ hγ
    by_contra hn
    have hmem := sourceKPChartTest_mem_upperSupport K φ.val (γ⁻¹ • x.val) hγ
    obtain ⟨z,hz,he⟩ := hmem
    obtain ⟨y,hy,hyz⟩ := φ.prop hz
    have hye : y = γ⁻¹ • x.val := by
      exact (sourceKPArchUpperEuclideanMap_left_inverse K y).symm.trans
        ((congrArg (sourceKPArchEuclideanUpperMap K) hyz).trans he)
    rw [hye] at hy
    exact (Set.disjoint_left.mp ((sourceKPUpperFiniteChart K hζ b p).separated γ hn))
      (by exact ⟨γ⁻¹ • x.val,hy,smul_inv_smul γ x.val⟩) x.prop
  rw [← tsum_subtype_eq_of_support_subset hs]
  change (∑' γ : SourceKPFiniteChartStabilizer K hζ b p,
    sourceKPChartPeriodTerm K hζ b φ.val γ.val x.val) = _
  rw [tsum_fintype]
  simpa only [sourceKPChartPeriodTerm,Equiv.inv_apply,Subgroup.coe_inv] using
    Equiv.sum_comp (Equiv.inv (SourceKPFiniteChartStabilizer K hζ b p))
      (fun γ => φ.val.val (sourceKPArchUpperEuclideanMap K (γ.val • x.val)))

theorem sourceKPChartPeriodizationCore_local_average (φ : SourceKPFiniteChartTests K hζ b p)
    (x : (sourceKPUpperFiniteChart K hζ b p).domain) :
    (sourceKPChartPeriodizationCore K hζ b φ.val).val (sourceKPFiniteChartProjection K hζ b p x) =
      (Fintype.card (SourceKPFiniteChartStabilizer K hζ b p) : ℂ) •
        (sourceKPFiniteChartTestAverage K hζ b p φ).val.val (sourceKPArchUpperEuclideanMap K x.val) := by
  rw [sourceKPChartPeriodizationCore_local_sum,sourceKPFiniteChartTestAverage_apply]
  · simp only [sourceKPArchEuclideanAction,sourceKPArchUpperEuclideanMap_left_inverse]
    rw [smul_smul,mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),one_smul]
    rfl
  · exact sourceKPFiniteChartCoordinateDomain_upper K hζ b p ⟨x.val,x.prop,rfl⟩

end
end ArtinMatthews
