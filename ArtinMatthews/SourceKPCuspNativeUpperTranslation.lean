module

public import ArtinMatthews.SourceKPCuspNativeHorizontal
public import ArtinMatthews.SourceArchSphericalProductCasimir
public import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacterLattice
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

/-! Translation by the actual archimedean unipotent is affine horizontal
translation in the product upper-half-space chart. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix OAI.CubicEisenstein
open SourceArchJacquet SourceHyperbolicGreen
open OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction
open scoped NumberField MatrixGroups AdeleRing ContDiff Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => mixedEmbedding.mixedSpace K
local notation "P" => ProductSpace (InfinitePlace K)

private theorem cuspUpperSection_translate (z w : ℂ) (y : ℝ) (hy : 0 < y) :
    sourceKPUpperMatrix ℂ w * (upperSection z y hy : GL (Fin 2) ℂ) =
      (upperSection (z+w) y hy : GL (Fin 2) ℂ) := by
  apply GeneralLinearGroup.ext
  intro i j
  change ((!![1,w;0,1] : Matrix (Fin 2) (Fin 2) ℂ) *
      !![(Real.sqrt y : ℂ),z / (Real.sqrt y : ℂ);0,(Real.sqrt y : ℂ)⁻¹]) i j =
        !![(Real.sqrt y : ℂ),(z+w) / (Real.sqrt y : ℂ);0,(Real.sqrt y : ℂ)⁻¹] i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,div_eq_mul_inv]
  all_goals ring

def sourceKPCuspNativePoint (p : P) (x : E) : P :=
  letI := source_isTotallyComplex K hζ
  p + sourceKPCuspProductHorizontalCLM K x

theorem sourceKPCuspNativePoint_height (p : P) (x : E) (v : InfinitePlace K) :
    sourceKPCuspNativePoint K hζ p x v 2 = p v 2 := by
  letI := source_isTotallyComplex K hζ
  change p v 2 + sourceKPCuspProductHorizontalCLM K x v 2 = _
  rw [sourceKPCuspProductHorizontalCLM_height,add_zero]

theorem sourceKPCuspNativePoint_contDiff (p : P) :
    ContDiff ℝ (∞ : ℕ∞ω) (sourceKPCuspNativePoint K hζ p) := by
  letI := source_isTotallyComplex K hζ
  exact contDiff_const.add (sourceKPCuspProductHorizontalCLM K).contDiff

theorem sourceKPArchComplex_mixedCoordinate (x : E) (v : InfinitePlace K) :
    letI := source_isTotallyComplex K hζ
    sourceKPArchComplexEquiv K hζ v ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x v) =
      sourceKPCuspComplexProjection K v x := by
  letI := source_isTotallyComplex K hζ
  have he := congrArg (fun u : E => u.2 ⟨v,IsTotallyComplex.isComplex v⟩)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply x)
  simpa only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply,sourceKPArchComplexEquiv,
    sourceArchCompletionEquiv,InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply,
    sourceKPCuspComplexProjection_apply] using he

theorem sourceKPCuspNativePoint_shift (p : P) (x : E) (v : InfinitePlace K) :
    letI := source_isTotallyComplex K hζ
    ((sourceKPCuspNativePoint K hζ p x v 0 : ℝ) : ℂ) +
      ((sourceKPCuspNativePoint K hζ p x v 1 : ℝ) : ℂ)*Complex.I =
        ((p v 0 : ℂ)+(p v 1 : ℂ)*Complex.I) + sourceKPCuspComplexProjection K v x := by
  letI := source_isTotallyComplex K hζ
  change ((p v 0 + sourceKPCuspProductHorizontalCLM K x v 0 : ℝ) : ℂ) +
      ((p v 1 + sourceKPCuspProductHorizontalCLM K x v 1 : ℝ) : ℂ)*Complex.I = _
  rw [sourceKPCuspProductHorizontalCLM_re,sourceKPCuspProductHorizontalCLM_im]
  calc
    _ = ((p v 0 : ℂ)+(p v 1 : ℂ)*Complex.I) +
        (((sourceKPCuspComplexProjection K v x).re : ℂ) +
          ((sourceKPCuspComplexProjection K v x).im : ℂ)*Complex.I) := by push_cast; ring
    _ = _ := by rw [Complex.re_add_im]

theorem sourceKPCuspNativeUpperSection_translate (p : P) (hp : ∀ v, 0 < p v 2) (x : E) :
    sourceKPUpperMatrix (InfiniteAdeleRing K) ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x) *
      sourceArchUpperHalfspaceMatrix K hζ p hp =
        sourceArchUpperHalfspaceMatrix K hζ (sourceKPCuspNativePoint K hζ p x)
          (fun v => by rw [sourceKPCuspNativePoint_height]; exact hp v) := by
  letI := source_isTotallyComplex K hζ
  apply (sourceArchGLPiEquiv K).injective
  funext v
  apply (sourceKPArchMatrixComplexEquiv K hζ v).injective
  simp only [map_mul,Pi.mul_apply,sourceArchUpperHalfspaceMatrix,MulEquiv.apply_symm_apply]
  have hu : sourceKPArchMatrixComplexEquiv K hζ v
      (sourceArchGLPiEquiv K (sourceKPUpperMatrix (InfiniteAdeleRing K)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)) v) =
      sourceKPUpperMatrix ℂ (sourceKPCuspComplexProjection K v x) := by
    change GeneralLinearGroup.map ((sourceKPArchComplexEquiv K hζ v).toRingHom.comp
      (sourceArchAdeleEval K v)) (sourceKPUpperMatrix (InfiniteAdeleRing K)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)) = _
    rw [sourceKPUpperMatrix_map]
    congr 1
    exact sourceKPArchComplex_mixedCoordinate K hζ x v
  rw [hu]
  simpa only [sourceKPCuspNativePoint_shift,sourceKPCuspNativePoint_height] using
    cuspUpperSection_translate ((p v 0 : ℂ)+(p v 1 : ℂ)*Complex.I)
      (sourceKPCuspComplexProjection K v x) (p v 2) (hp v)

theorem sourceKPCuspNativeUpperLift_translate (p : P) (hp : ∀ v, 0 < p v 2) (x : E)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPAdelicUpperLift K hζ (mixedAdelicAdd K x) *
      (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),qf) =
        (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ (sourceKPCuspNativePoint K hζ p x)
          (fun v => by rw [sourceKPCuspNativePoint_height]; exact hp v)),qf) := by
  apply Prod.ext
  · change ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)) *
      ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp) = _
    rw [← map_mul,sourceKPCuspNativeUpperSection_translate]
  · change sourceKPFiniteAdeleUpperLift K hζ 0*qf = qf
    rw [sourceKPFiniteAdeleUpperLift_zero,one_mul]

end
end ArtinMatthews
