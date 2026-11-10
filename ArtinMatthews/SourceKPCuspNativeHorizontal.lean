module

public import ArtinMatthews.SourceKPCuspTraceFunctional
public import ArtinMatthews.SourceHyperbolicProductCalculus
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Minkowski horizontal directions are the native Cartesian
horizontal directions in the product of upper half spaces. -/
namespace ArtinMatthews
open NumberField Module OAI.CubicEisenstein SourceHyperbolicGreen
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
local notation "E" => mixedEmbedding.mixedSpace K
local notation "P" => ProductSpace (InfinitePlace K)

def sourceKPCuspComplexProjection (v : InfinitePlace K) : E →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj ⟨v,IsTotallyComplex.isComplex v⟩).comp (ContinuousLinearMap.snd ℝ _ _)

theorem sourceKPCuspComplexProjection_apply (v : InfinitePlace K) (x : E) :
    sourceKPCuspComplexProjection K v x = x.2 ⟨v,IsTotallyComplex.isComplex v⟩ := rfl

def sourceKPCuspProductHorizontalCLM : E →L[ℝ] P :=
  ContinuousLinearMap.pi fun v =>
    (Complex.reCLM.comp (sourceKPCuspComplexProjection K v)).smulRight (euclideanCoordinateVector 0) +
    (Complex.imCLM.comp (sourceKPCuspComplexProjection K v)).smulRight (euclideanCoordinateVector 1)

theorem sourceKPCuspProductHorizontalCLM_apply (x : E) (v : InfinitePlace K) :
    sourceKPCuspProductHorizontalCLM K x v =
      (sourceKPCuspComplexProjection K v x).re • euclideanCoordinateVector 0 +
      (sourceKPCuspComplexProjection K v x).im • euclideanCoordinateVector 1 := rfl

theorem sourceKPCuspProductHorizontalCLM_re (x : E) (v : InfinitePlace K) :
    sourceKPCuspProductHorizontalCLM K x v 0 = (sourceKPCuspComplexProjection K v x).re := by
  simp [sourceKPCuspProductHorizontalCLM_apply,euclideanCoordinateVector]

theorem sourceKPCuspProductHorizontalCLM_im (x : E) (v : InfinitePlace K) :
    sourceKPCuspProductHorizontalCLM K x v 1 = (sourceKPCuspComplexProjection K v x).im := by
  simp [sourceKPCuspProductHorizontalCLM_apply,euclideanCoordinateVector]

theorem sourceKPCuspProductHorizontalCLM_height (x : E) (v : InfinitePlace K) :
    sourceKPCuspProductHorizontalCLM K x v 2 = 0 := by
  simp [sourceKPCuspProductHorizontalCLM_apply,euclideanCoordinateVector]

theorem sourceKPCuspProductHorizontalCLM_direction (v : InfinitePlace K) (k : Fin 2) :
    sourceKPCuspProductHorizontalCLM K (sourceKPCuspHorizontalDirection K v k) =
      productDirection v k.castSucc := by
  funext w
  rw [sourceKPCuspProductHorizontalCLM_apply,productDirection]
  by_cases hw : w = v
  · subst w
    rw [Pi.single_eq_same]
    fin_cases k
    · rw [sourceKPCuspComplexProjection_apply,← mixedEmbedding.stdBasis_apply_isComplex_fst,
        ← mixedEmbedding.stdBasis_apply_isComplex_snd]
      simp [sourceKPCuspHorizontalDirection, Basis.repr_self,Finsupp.single_apply]
    · rw [sourceKPCuspComplexProjection_apply,← mixedEmbedding.stdBasis_apply_isComplex_fst,
        ← mixedEmbedding.stdBasis_apply_isComplex_snd]
      simp [sourceKPCuspHorizontalDirection, Basis.repr_self,Finsupp.single_apply]
  · rw [Pi.single_eq_of_ne hw,sourceKPCuspComplexProjection_apply,
      ← mixedEmbedding.stdBasis_apply_isComplex_fst,← mixedEmbedding.stdBasis_apply_isComplex_snd]
    simp [sourceKPCuspHorizontalDirection,Basis.repr_self,Finsupp.single_apply,hw,Ne.symm hw]

end
end ArtinMatthews
