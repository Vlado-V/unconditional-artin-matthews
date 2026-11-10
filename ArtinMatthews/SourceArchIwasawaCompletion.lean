module

public import ArtinMatthews.SourceArchIwasawa
public import ArtinMatthews.SourceArchAdelicEmbedding
public import ArtinMatthews.SourceArchCompletedMeasure
public import ArtinMatthews.SourceKPRingBorel
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The complex Gram factors at all infinite completions. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPArchComplexEquiv (v : InfinitePlace K) : v.Completion ≃+* ℂ := by
  letI := source_isTotallyComplex K hζ
  exact sourceArchCompletionEquiv K v (NumberField.IsTotallyComplex.isComplex v)

def sourceKPArchMatrixComplexEquiv (v : InfinitePlace K) :
    GL (Fin 2) v.Completion ≃* GL (Fin 2) ℂ :=
  Units.mapEquiv (sourceKPArchComplexEquiv K hζ v).mapMatrix.toMulEquiv

theorem sourceKPArchMatrixComplexEquiv_apply (v : InfinitePlace K)
    (g : GL (Fin 2) v.Completion) (i j : Fin 2) :
    sourceKPArchMatrixComplexEquiv K hζ v g i j =
      sourceKPArchComplexEquiv K hζ v (g i j) := rfl

theorem sourceKPArchMatrixComplexEquiv_scalar (v : InfinitePlace K) (u : v.Completionˣ) :
    sourceKPArchMatrixComplexEquiv K hζ v (GeneralLinearGroup.scalar (Fin 2) u) =
      GeneralLinearGroup.scalar (Fin 2) (Units.map (sourceKPArchComplexEquiv K hζ v) u) :=
  by
    apply GeneralLinearGroup.ext
    intro i j
    change (sourceKPArchComplexEquiv K hζ v)
      (Matrix.diagonal (fun _ : Fin 2 => (u : v.Completion)) i j) =
        Matrix.diagonal (fun _ : Fin 2 => sourceKPArchComplexEquiv K hζ v (u : v.Completion)) i j
    by_cases hij : i = j <;> simp [hij]

def sourceKPArchIwasawaBorel (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    GL (Fin 2) (InfiniteAdeleRing K) :=
  (sourceArchGLPiEquiv K).symm (fun v => (sourceKPArchMatrixComplexEquiv K hζ v).symm
    (sourceArchIwasawaBorel (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v))))

def sourceKPArchIwasawaCompact (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    GL (Fin 2) (InfiniteAdeleRing K) :=
  (sourceArchGLPiEquiv K).symm (fun v => (sourceKPArchMatrixComplexEquiv K hζ v).symm
    (sourceArchUnitaryGL (sourceArchIwasawaUnitary
      (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)))))

def sourceKPArchIwasawaScalar (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    (InfiniteAdeleRing K)ˣ :=
  MulEquiv.piUnits.symm (fun v => Units.map (sourceKPArchComplexEquiv K hζ v).symm
    (sourceArchIwasawaScalar (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v))))

theorem sourceKPArchIwasawaBorel_at (g : GL (Fin 2) (InfiniteAdeleRing K))
    (v : InfinitePlace K) :
    sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K (sourceKPArchIwasawaBorel K hζ g) v) =
      sourceArchIwasawaBorel (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) := by
  simp only [sourceKPArchIwasawaBorel, MulEquiv.apply_symm_apply]

theorem sourceKPArchIwasawaCompact_at (g : GL (Fin 2) (InfiniteAdeleRing K))
    (v : InfinitePlace K) :
    sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K (sourceKPArchIwasawaCompact K hζ g) v) =
      sourceArchUnitaryGL (sourceArchIwasawaUnitary
        (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v))) := by
  simp only [sourceKPArchIwasawaCompact, MulEquiv.apply_symm_apply]

theorem sourceKPArchIwasawaScalar_at (g : GL (Fin 2) (InfiniteAdeleRing K))
    (v : InfinitePlace K) :
    Units.map (sourceKPArchComplexEquiv K hζ v)
      (MulEquiv.piUnits (sourceKPArchIwasawaScalar K hζ g) v) =
        sourceArchIwasawaScalar (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) := by
  simp only [sourceKPArchIwasawaScalar, MulEquiv.apply_symm_apply]
  apply Units.ext
  exact (sourceKPArchComplexEquiv K hζ v).apply_symm_apply _

theorem sourceKPArchIwasawaBorel_mem (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    sourceKPArchIwasawaBorel K hζ g ∈ sourceKPRingNormalizedBorel (InfiniteAdeleRing K) := by
  constructor
  · funext v
    apply (sourceKPArchComplexEquiv K hζ v).injective
    change (sourceKPArchComplexEquiv K hζ v) ((sourceKPArchIwasawaBorel K hζ g) 1 0 v) =
      (sourceKPArchComplexEquiv K hζ v) (0 : v.Completion)
    rw [map_zero]
    exact (congrArg (fun a : GL (Fin 2) ℂ => a 1 0)
      (sourceKPArchIwasawaBorel_at K hζ g v)).trans (sourceArchIwasawaBorel_mem _).1
  · funext v
    apply (sourceKPArchComplexEquiv K hζ v).injective
    change (sourceKPArchComplexEquiv K hζ v) ((sourceKPArchIwasawaBorel K hζ g) 1 1 v) =
      (sourceKPArchComplexEquiv K hζ v) (1 : v.Completion)
    rw [map_one]
    exact (congrArg (fun a : GL (Fin 2) ℂ => a 1 1)
      (sourceKPArchIwasawaBorel_at K hζ g v)).trans (sourceArchIwasawaBorel_mem _).2

theorem sourceKPArchIwasawa_factor (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    g = sourceKPArchIwasawaBorel K hζ g *
      GeneralLinearGroup.scalar (Fin 2) (sourceKPArchIwasawaScalar K hζ g) *
        sourceKPArchIwasawaCompact K hζ g := by
  apply (sourceArchGLPiEquiv K).injective
  funext v
  apply (sourceKPArchMatrixComplexEquiv K hζ v).injective
  simp only [map_mul, Pi.mul_apply, sourceArchGLPiEquiv_scalar,
    sourceKPArchMatrixComplexEquiv_scalar, sourceKPArchIwasawaBorel_at,
    sourceKPArchIwasawaScalar_at, sourceKPArchIwasawaCompact_at]
  exact sourceArchIwasawa_factor _

end
end ArtinMatthews
