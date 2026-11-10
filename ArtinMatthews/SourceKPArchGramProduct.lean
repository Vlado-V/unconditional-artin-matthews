module

public import ArtinMatthews.SourceArchGramCoordinates
public import ArtinMatthews.SourceArchIwasawaCompletion
public import ArtinMatthews.SourceArchGramNormalForm
public import ArtinMatthews.SourceArchSectionContinuity
public import ArtinMatthews.SourceKPAdelicBaseCompactTopology
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

/-! Product Gram coordinates and their literal archimedean matrix section. -/
namespace ArtinMatthews
open NumberField Matrix Matrix.GeneralLinearGroup SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

abbrev SourceKPArchUpperHalfSpace := InfinitePlace K → SourceArchUpperHalfSpace

def sourceKPArchGramCoordinatesMatrix (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    SourceKPArchUpperHalfSpace K :=
  fun v => sourceArchGramCoordinates
    (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v))

theorem sourceKPArchGramCoordinatesMatrix_continuous :
    Continuous (sourceKPArchGramCoordinatesMatrix K hζ) := by
  apply continuous_pi
  intro v
  exact sourceArchGramCoordinates_continuous.comp (sourceArchMatrixAt_continuous K hζ v)

theorem sourceKPArchGramCoordinatesMatrix_scalar (g : GL (Fin 2) (InfiniteAdeleRing K))
    (u : (InfiniteAdeleRing K)ˣ) :
    sourceKPArchGramCoordinatesMatrix K hζ (g * GeneralLinearGroup.scalar (Fin 2) u) =
      sourceKPArchGramCoordinatesMatrix K hζ g := by
  funext v
  simp only [sourceKPArchGramCoordinatesMatrix, map_mul, Pi.mul_apply,
    sourceArchGLPiEquiv_scalar, sourceKPArchMatrixComplexEquiv_scalar,
    sourceArchGramCoordinates_scalar]

def sourceKPArchUpperHalfSection (p : SourceKPArchUpperHalfSpace K) :
    GL (Fin 2) (InfiniteAdeleRing K) :=
  (sourceArchGLPiEquiv K).symm (fun v => (sourceKPArchMatrixComplexEquiv K hζ v).symm
    (sourceArchUpperHalfSection (p v)))

theorem sourceKPArchUpperHalfSection_at (p : SourceKPArchUpperHalfSpace K)
    (v : InfinitePlace K) :
    sourceKPArchMatrixComplexEquiv K hζ v
      (sourceArchGLPiEquiv K (sourceKPArchUpperHalfSection K hζ p) v) =
        sourceArchUpperHalfSection (p v) := by
  simp only [sourceKPArchUpperHalfSection, MulEquiv.apply_symm_apply]

theorem sourceKPArchUpperHalfSection_continuous :
    Continuous (sourceKPArchUpperHalfSection K hζ) := by
  apply (sourceKPArchGLPiEquiv_symm_continuous K).comp
  apply continuous_pi
  intro v
  exact (sourceKPArchMatrixComplexEquiv_symm_continuous K hζ v).comp
    (sourceArchUpperHalfSection_continuous.comp (continuous_apply v))

theorem sourceKPArchGramCoordinatesMatrix_section (p : SourceKPArchUpperHalfSpace K) :
    sourceKPArchGramCoordinatesMatrix K hζ (sourceKPArchUpperHalfSection K hζ p) = p := by
  funext v
  rw [sourceKPArchGramCoordinatesMatrix, sourceKPArchUpperHalfSection_at,
    sourceArchGramCoordinates_section]

def sourceKPArchUnitaryMatrix (k : InfinitePlace K → Matrix.unitaryGroup (Fin 2) ℂ) :
    GL (Fin 2) (InfiniteAdeleRing K) :=
  (sourceArchGLPiEquiv K).symm (fun v => (sourceKPArchMatrixComplexEquiv K hζ v).symm
    (sourceArchUnitaryGL (k v)))

theorem sourceKPArchUnitaryMatrix_at (k : InfinitePlace K → Matrix.unitaryGroup (Fin 2) ℂ)
    (v : InfinitePlace K) :
    sourceKPArchMatrixComplexEquiv K hζ v
      (sourceArchGLPiEquiv K (sourceKPArchUnitaryMatrix K hζ k) v) =
        sourceArchUnitaryGL (k v) := by
  simp only [sourceKPArchUnitaryMatrix, MulEquiv.apply_symm_apply]

theorem sourceKPArchGramCoordinatesMatrix_unitary (g : GL (Fin 2) (InfiniteAdeleRing K))
    (k : InfinitePlace K → Matrix.unitaryGroup (Fin 2) ℂ) :
    sourceKPArchGramCoordinatesMatrix K hζ (g * sourceKPArchUnitaryMatrix K hζ k) =
      sourceKPArchGramCoordinatesMatrix K hζ g := by
  funext v
  simp only [sourceKPArchGramCoordinatesMatrix, map_mul, Pi.mul_apply,
    sourceKPArchUnitaryMatrix_at, sourceArchGramCoordinates_unitary]

theorem sourceKPArchGramMatrix_normal_form (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    ∃ (u : (InfiniteAdeleRing K)ˣ) (k : InfinitePlace K → Matrix.unitaryGroup (Fin 2) ℂ),
      g = sourceKPArchUpperHalfSection K hζ (sourceKPArchGramCoordinatesMatrix K hζ g) *
        GeneralLinearGroup.scalar (Fin 2) u * sourceKPArchUnitaryMatrix K hζ k := by
  choose u k hk using (fun v : InfinitePlace K => sourceArch_gram_normal_form
    (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)))
  let d : (InfiniteAdeleRing K)ˣ := MulEquiv.piUnits.symm
    (fun v => Units.map (sourceKPArchComplexEquiv K hζ v).symm (u v))
  have hd (v : InfinitePlace K) :
      Units.map (sourceKPArchComplexEquiv K hζ v) (MulEquiv.piUnits d v) = u v := by
    dsimp only [d]
    rw [MulEquiv.apply_symm_apply]
    apply Units.ext
    exact (sourceKPArchComplexEquiv K hζ v).apply_symm_apply _
  refine ⟨d, k, ?_⟩
  apply (sourceArchGLPiEquiv K).injective
  funext v
  apply (sourceKPArchMatrixComplexEquiv K hζ v).injective
  simp only [map_mul, Pi.mul_apply, sourceArchGLPiEquiv_scalar,
    sourceKPArchMatrixComplexEquiv_scalar, sourceKPArchUpperHalfSection_at,
    sourceKPArchUnitaryMatrix_at, hd]
  exact hk v

end
end ArtinMatthews
