module

public import ArtinMatthews.SourceKPCompactChartMassLift
public import ArtinMatthews.SourceKPChartPeriodizationCore
public import ArtinMatthews.SourceKPCompactCoreMass
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import ArtinMatthews.SourceKPChartPeriodizationAverage
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

/-! Periodized chart tests pair with quotient mass by the exact stabilizer normalization. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen Filter
open scoped NumberField MatrixGroups AdeleRing Topology ENNReal Classical InnerProductSpace ComplexConjugate
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)

local notation "X" => ProductSpace (InfinitePlace K)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "U" => sourceKPFiniteChartCoordinateDomain K hζ b p
local notation "R" => Set.range (sourceKPFiniteChartProjection K hζ b p)
local notation "H" => SourceKPFiniteChartStabilizer K hζ b p
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "ν" => productVolume (InfinitePlace K)

theorem sourceKPCompactCoreMass_inner (f : sourceKPCompactC2Core K hζ) (g : Lp ℂ 2 μ) :
    inner ℂ (sourceKPCompactCoreMass K hζ 2 f) g =
      ∫ y, inner ℂ (f.val y) (g y) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sourceKPCompactCoreMass_coe K hζ f] with y hy
  rw [hy]

theorem sourceKPCompactChartMassLift_inner (φ : SourceKPFiniteChartTests K hζ b p) (g : Lp ℂ 2 μ) :
    inner ℂ (h1LocalTestMass U φ).val (sourceKPCompactChartMassLift K hζ b p g).val =
      inner ℂ (sourceKPCompactCoreMass K hζ 2 (sourceKPChartPeriodizationCore K hζ b φ.val)) g := by
  let T := sourceKPChartPeriodizationCore K hζ b φ.val
  let A := sourceKPFiniteChartTestAverage K hζ b p φ
  let G := sourceKPCompactChartMassLift K hζ b p g
  let q := sourceKPCompactCoordinateProjection K hζ b
  let n : ℝ≥0∞ := Nat.card H
  let hν := sourceKPCompactCoordinateProjection_measurePreserving K hζ b p
  have hI (γ : H) : inner ℂ (h1LocalTestMass U (sourceKPFiniteChartTestPullback K hζ b p γ φ)).val G.val =
      inner ℂ (h1LocalTestMass U φ).val G.val := by
    let L := sourceKPArchL2Pullback K hζ γ.val.val
    have hG := congrArg Subtype.val (sourceKPCompactChartMassLift_invariant K hζ b p g γ)
    change L G.val = G.val at hG
    change inner ℂ (h1TestMass (sourceKPArchTestPullback K hζ γ.val.val φ.val)) G.val = _
    rw [sourceKPArchL2Pullback_core]
    change inner ℂ (L (h1TestMass φ.val)) G.val = inner ℂ (h1TestMass φ.val) G.val
    calc
      _ = inner ℂ (L (h1TestMass φ.val)) (L G.val) := by rw [hG]
      _ = _ := L.inner_map_map _ _
  have hA : inner ℂ (h1LocalTestMass U A).val G.val = inner ℂ (h1LocalTestMass U φ).val G.val := by
    change inner ℂ ((h1SupportedMass U).subtype
      (h1LocalTestMass U (sourceKPFiniteChartTestAverage K hζ b p φ))) G.val = _
    simp only [sourceKPFiniteChartTestAverage,LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,
      inner_smul_left,sum_inner]
    change conj ((Fintype.card H : ℂ)⁻¹) *
      (∑ γ : H, inner ℂ (h1LocalTestMass U (sourceKPFiniteChartTestPullback K hζ b p γ φ)).val G.val) = _
    simp_rw [hI]
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,map_inv₀,map_natCast,← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),one_mul]
  rw [← hA,sourceKPCompactCoreMass_inner,L2.inner_def]
  let J : Y → ℂ := fun y => inner ℂ (T.val y) (g y)
  let L : X → ℂ := fun x => inner ℂ (A.val.val x) (g (q x))
  have hJ : AEStronglyMeasurable J ((μ).restrict R) :=
    ((T.prop.1.aestronglyMeasurable).inner (Lp.aestronglyMeasurable g)).mono_measure
      Measure.restrict_le_self
  have hu := (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p).measurableSet
  have hr := (sourceKPFiniteChart_range_open K hζ b p).measurableSet
  have hi : (∫ x, inner ℂ ((h1LocalTestMass U A).val x) (G.val x) ∂ν) = ∫ x in U, L x ∂ν := by
    rw [← integral_indicator hu]
    apply integral_congr_ae
    filter_upwards [h1TestMass_coe A.val,sourceKPCompactChartMassLift_coe K hζ b p g] with x hx hg
    change inner ℂ ((h1TestMass A.val) x) (G.val x) = (U).indicator L x
    rw [hx,hg]
    by_cases hxu : x ∈ U
    · simp only [Set.indicator_of_mem hxu,L,Function.comp_apply,q]
    · simp only [Set.indicator_of_notMem hxu,inner_zero_right]
  have hzero : (∫ y, J y ∂μ) = ∫ y in R, J y ∂μ := by
    rw [← integral_indicator hr]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      by_cases hy : y ∈ R
      · simp only [Set.indicator_of_mem hy]
      · have hz : T.val y = 0 := by
          by_contra hn
          exact hy (sourceKPChartPeriodizationCore_support K hζ b p φ (subset_tsupport T.val hn))
        simp only [Set.indicator_of_notMem hy,J,hz,inner_zero_left]
  have hscale :
      (∫ x, J (q x) ∂(n⁻¹ • (ν).restrict U)) =
        (n.toReal⁻¹ : ℝ) • ∫ x in U, J (q x) ∂ν := by
    rw [integral_smul_measure,ENNReal.toReal_inv]
  have heq : (∫ x in U, J (q x) ∂ν) = (Fintype.card H : ℂ) * ∫ x in U, L x ∂ν := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hu] with x hx
    obtain ⟨z,hz,rfl⟩ := hx
    let zD : (sourceKPUpperFiniteChart K hζ b p).domain := ⟨z,hz⟩
    have hzq : q (sourceKPArchUpperEuclideanMap K z) = sourceKPFiniteChartProjection K hζ b p zD := by
      unfold q sourceKPCompactCoordinateProjection
      rw [sourceKPArchUpperEuclideanMap_left_inverse]
      rfl
    simp only [J,L,hzq]
    rw [sourceKPChartPeriodizationCore_local_average K hζ b p φ zD,inner_smul_left]
    rw [← Complex.ofReal_natCast,Complex.conj_ofReal]
  have hn : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcomp : (∫ y in R, J y ∂μ) = ∫ x, J (q x) ∂(n⁻¹ • (ν).restrict U) := by
    have hm : Measure.map q (n⁻¹ • (ν).restrict U) = (μ).restrict R := hν.map_eq
    rw [← hm]
    exact integral_map hν.measurable.aemeasurable (hm.symm ▸ hJ)
  have hcard : (n.toReal : ℂ) = (Fintype.card H : ℂ) := by
    change (((Nat.card H : ℝ≥0∞).toReal : ℝ) : ℂ) = _
    rw [ENNReal.toReal_natCast,Complex.ofReal_natCast,Nat.card_eq_fintype_card]
  change (∫ x, inner ℂ ((h1LocalTestMass U A).val x) (G.val x) ∂ν) = ∫ y, J y ∂μ
  rw [hi,hzero,hcomp,hscale,heq,Complex.real_smul,Complex.ofReal_inv,hcard,
    ← mul_assoc,inv_mul_cancel₀ hn,one_mul]

end
end ArtinMatthews
