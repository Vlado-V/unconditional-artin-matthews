module

public import ArtinMatthews.SourceArchCompletedJacquet
public import ArtinMatthews.SourceArchSectionFactorization
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

/-! The product diagonal in the actual infinite adeles and its exact local Jacquet coordinates. -/
namespace ArtinMatthews
open NumberField Matrix StandardAdelic SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPArchJacquetDiagonalUnits (y : (v : InfinitePlace K) → v.Completionˣ) :
    (InfiniteAdeleRing K)ˣ where
  val := fun v => (y v : v.Completion)
  inv := fun v => (y v).inv
  val_inv := by
    funext v
    change (y v : v.Completion)*(y v).inv = 1
    exact (y v).val_inv
  inv_val := by
    funext v
    change (y v).inv*(y v : v.Completion) = 1
    exact (y v).inv_val

def sourceKPArchJacquetDiagonal (y : (v : InfinitePlace K) → v.Completionˣ) :
    PGL(2,InfiniteAdeleRing K) :=
  sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) (sourceKPArchJacquetDiagonalUnits K y)

theorem sourceKPArchJacquetDiagonal_at (y : (v : InfinitePlace K) → v.Completionˣ)
    (v : InfinitePlace K) (hv : InfinitePlace.IsComplex v) :
    sourceArchProjectiveAt K hζ v (sourceKPArchJacquetDiagonal K y) =
      sourcePGL2Diagonal (Units.map (sourceArchCompletionEquiv K v hv).toMonoidHom (y v)) := by
  let e := (sourceKPArchComplexEquiv K hζ v).toRingHom.comp (sourceArchAdeleEval K v)
  change ProjGenLinGroup.map e (sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K)
    (sourceKPArchJacquetDiagonalUnits K y)) = _
  rw [sourceKPProjectiveDiagonalHom_map]
  have hu : Units.map e.toMonoidHom (sourceKPArchJacquetDiagonalUnits K y) =
      Units.map (sourceArchCompletionEquiv K v hv).toMonoidHom (y v) := by
    apply Units.ext
    rfl
  rw [hu]
  change ProjGenLinGroup.mk (sourceKPDiagonalHom ℂ _) = ProjGenLinGroup.mk (sourceGL2Diagonal _)
  rw [sourceKPDiagonalHom_field]

theorem sourceKPArchJacquetDiagonal_localSection (s : ℂ)
    (y : (v : InfinitePlace K) → v.Completionˣ) (v : InfinitePlace K)
    (hv : InfinitePlace.IsComplex v) (x : v.Completion) :
    sourceArchSphericalSection s
      (sourcePGL2Weyl * sourcePGL2Upper (sourceKPArchComplexEquiv K hζ v x) *
        sourceArchProjectiveAt K hζ v (sourceKPArchJacquetDiagonal K y)) =
      sourceArchCompletedSphericalSection K v hv s
        (sourcePGL2Weyl * sourcePGL2Upper x * sourcePGL2Diagonal (y v)) := by
  rw [sourceKPArchJacquetDiagonal_at K hζ y v hv,sourceArchCompletedSphericalSection_bigCell]
  rfl

theorem sourceKPLocalInfiniteCharacter_star (v : InfinitePlace K) (x : v.Completion) :
    star (localInfiniteCharacter K v x) = localInfiniteCharacter K v (-x) := by
  rw [AddChar.map_neg_eq_inv]
  have h : ‖localInfiniteCharacter K v x‖ = 1 := by
    rw [localInfiniteCharacter_single]
    exact archCharacter_unitary K _
  exact (Complex.inv_eq_conj h).symm

end
end ArtinMatthews
