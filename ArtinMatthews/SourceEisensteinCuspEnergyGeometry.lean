module

public import ArtinMatthews.SourceKPCuspNativeUpperTranslation
public import ArtinMatthews.SourceAdelicHeightFibers
public import ArtinMatthews.SourceEisensteinNativeEnergy
public import ArtinMatthews.SourceKPFiniteHeightNormalization
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

/-! Actual high-cusp height and native horizontal motion on a fixed
finite-level fiber. The finite height factor is retained. -/
namespace ArtinMatthews
open NumberField Matrix SourceArchJacquet OAI.CubicEisenstein SourceHyperbolicGreen
open OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "P" => ProductSpace (InfinitePlace K)
local notation "E" => mixedEmbedding.mixedSpace K
local notation "G" => PGL(2,InfiniteAdeleRing K)

def sourceKPCuspHeightGapExponent : ℝ := 1 / (InfinitePlace.nrComplexPlaces K : ℝ)

include hζ in
theorem sourceKPCuspHeightGapExponent_pos : 0 < sourceKPCuspHeightGapExponent K := by
  let := source_isTotallyComplex K hζ
  have hc : Fintype.card (InfinitePlace K) = InfinitePlace.nrComplexPlaces K := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,IsTotallyComplex.nrRealPlaces_eq_zero,zero_add]
  have hr : 0 < (InfinitePlace.nrComplexPlaces K : ℝ) := by
    rw [← hc]
    exact_mod_cast Fintype.card_pos
  exact one_div_pos.mpr hr

theorem sourceKPAdelicCoverHeight_native_factor (a : G) (qf : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPAdelicCoverHeight K hζ (a,qf) = sourceKPAdelicCoverHeight K hζ (1,qf) *
      ∏ v, sourceKPArchNativeCoordinates K hζ a v 2 ^ 2 := by
  let := source_isTotallyComplex K hζ
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective a
  obtain ⟨u,hu⟩ := ProjGenLinGroup.mk_surjective (sourceKPFiniteAdeleProjectiveProjection K hζ qf)
  have hbase : sourceKPAdelicCoverHeight K hζ (1,qf) = sourceKPFiniteMatrixHeightProduct K u := by
    simpa only [map_one,sourceKPArchMatrixHeight_one,one_mul] using
      sourceKPAdelicCoverHeight_arch_matrix K hζ qf u hu.symm (1 : GL (Fin 2) (InfiniteAdeleRing K))
  rw [sourceKPAdelicCoverHeight_arch_matrix K hζ qf u hu.symm,hbase,
    mul_comm (sourceKPArchMatrixHeight K hζ g)]
  apply congrArg (sourceKPFiniteMatrixHeightProduct K u * ·)
  unfold sourceKPArchMatrixHeight
  apply Finset.prod_congr rfl
  intro v _
  rw [IsTotallyComplex.mult_eq,sourceKPArchNativeCoordinates,sourceKPArchGramCoordinates_mk]
  change _ = sourceArchUpperEuclideanMap (sourceKPArchGramCoordinatesMatrix K hζ g v) 2 ^ 2
  rw [sourceArchUpperEuclideanMap,sourceArchSpatialCoordinates_symm_apply]
  rfl

theorem sourceKPCuspNativeCoordinates_upper_mixed (a : G) (x : E) :
    sourceKPArchNativeCoordinates K hζ
      ((sourceKPAdelicUpperLift K hζ (mixedAdelicAdd K x)).1*a) =
        sourceKPCuspNativePoint K hζ (sourceKPArchNativeCoordinates K hζ a) x := by
  let p := sourceKPArchNativeCoordinates K hζ a
  have hp : ∀ v, 0 < p v 2 := fun v =>
    productUpper_pos (sourceKPArchNativeCoordinates_positive K hζ a) v
  have he := congrArg (fun q : SourceKPAdelicProjective K hζ => sourceKPArchNativeCoordinates K hζ q.1)
    (sourceKPCuspNativeUpperLift_translate K hζ p hp x 1)
  change sourceKPArchNativeCoordinates K hζ
      ((sourceKPAdelicUpperLift K hζ (mixedAdelicAdd K x)).1 *
        ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp)) =
    sourceKPArchNativeCoordinates K hζ
      (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ (sourceKPCuspNativePoint K hζ p x) _)) at he
  rw [sourceKPArchNativeCoordinates_mul,sourceKPArchNativeCoordinates_section,
    sourceKPArchNativeCoordinates_section] at he
  rw [sourceKPArchNativeCoordinates_mul]
  exact he

private theorem cuspMixedUpper_finite (x : E) :
    (sourceKPAdelicUpperLift K hζ (mixedAdelicAdd K x)).2 = 1 := by
  change sourceKPFiniteAdeleUpperLift K hζ 0 = 1
  exact sourceKPFiniteAdeleUpperLift_zero K hζ

theorem sourceKPAdelicNonconstantEnergy_upper_mixed (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (x : E) :
    sourceKPAdelicNonconstantEnergy K hζ s (sourceKPAdelicUpperLift K hζ (mixedAdelicAdd K x)*q) =
      productGradientEnergy (sourceKPAdelicNonconstantProductChart K hζ s (1,q.2))
        (sourceKPCuspNativePoint K hζ (sourceKPArchNativeCoordinates K hζ q.1) x) := by
  change productGradientEnergy
      (sourceKPAdelicNonconstantProductChart K hζ s
        (1,(sourceKPAdelicUpperLift K hζ (mixedAdelicAdd K x)).2*q.2))
      (sourceKPArchNativeCoordinates K hζ
        ((sourceKPAdelicUpperLift K hζ (mixedAdelicAdd K x)).1*q.1)) = _
  rw [cuspMixedUpper_finite K hζ x,one_mul,sourceKPCuspNativeCoordinates_upper_mixed]

theorem sourceKPAdelicNonconstantEisenstein_upper_mixed_native (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (x : E) :
    sourceKPAdelicNonconstantEisenstein K hζ s (sourceKPAdelicUpperLift K hζ (mixedAdelicAdd K x)*q) =
      sourceKPAdelicNonconstantProductChart K hζ s (1,q.2)
        (sourceKPCuspNativePoint K hζ (sourceKPArchNativeCoordinates K hζ q.1) x) := by
  have h := (sourceKPAdelicNonconstantProductChart_nativeCoordinates K hζ s
    (sourceKPAdelicUpperLift K hζ (mixedAdelicAdd K x)*q)).symm
  change _ = sourceKPAdelicNonconstantProductChart K hζ s
    (1,(sourceKPAdelicUpperLift K hζ (mixedAdelicAdd K x)).2*q.2)
    (sourceKPArchNativeCoordinates K hζ
      ((sourceKPAdelicUpperLift K hζ (mixedAdelicAdd K x)).1*q.1)) at h
  rw [cuspMixedUpper_finite K hζ x,one_mul,sourceKPCuspNativeCoordinates_upper_mixed] at h
  exact h

end
end ArtinMatthews
