module

public import ArtinMatthews.SourceArchSectionFactorization
public import ArtinMatthews.SourceArchSphericalContinuity
public import ArtinMatthews.SourceKPAdelicCompactIntersection
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
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceArchComplexEquiv_continuous (v : InfinitePlace K) :
    Continuous (sourceKPArchComplexEquiv K hζ v) := by
  apply Isometry.continuous
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, sourceKPArchComplexEquiv_norm]

theorem sourceArchMatrixAt_continuous (v : InfinitePlace K) :
    Continuous (fun g : GL (Fin 2) (InfiniteAdeleRing K) =>
      sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) := by
  let f : InfiniteAdeleRing K →+* ℂ :=
    (sourceKPArchComplexEquiv K hζ v).toRingHom.comp (sourceArchAdeleEval K v)
  have hf : Continuous f := (sourceArchComplexEquiv_continuous K hζ v).comp
    (_root_.continuous_apply v)
  have he : (fun g : GL (Fin 2) (InfiniteAdeleRing K) =>
      sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) =
        GeneralLinearGroup.map (n := Fin 2) f := by
    funext g
    apply GeneralLinearGroup.ext
    intro i j
    rfl
  rw [he]
  exact hf.generalLinearGroup_map (n := Fin 2)

theorem sourceArchSphericalProduct_matrix_continuous (s : ℂ) :
    Continuous (fun g : GL (Fin 2) (InfiniteAdeleRing K) =>
      sourceArchSphericalProduct K hζ s (ProjGenLinGroup.mk g)) := by
  simp_rw [sourceArchSphericalProduct_mk]
  apply continuous_finsetProd
  intro v _
  exact (sourceArchSphericalGL_continuous s).comp (sourceArchMatrixAt_continuous K hζ v)

theorem sourceArchCompactScalar_continuous (s : ℂ) (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun g : GL (Fin 2) (InfiniteAdeleRing K) =>
      sourceKPAdelicCompactScalar K hζ s (ProjGenLinGroup.mk g,qf)) := by
  have he : (fun g : GL (Fin 2) (InfiniteAdeleRing K) =>
      sourceKPAdelicCompactScalar K hζ s (ProjGenLinGroup.mk g,qf)) =
      fun g => sourceArchSphericalProduct K hζ s (ProjGenLinGroup.mk g) *
        sourceKPAdelicCompactScalar K hζ s (1,qf) := by
    funext g
    exact sourceArchCompactScalar_factor K hζ s (ProjGenLinGroup.mk g) qf
  rw [he]
  exact (sourceArchSphericalProduct_matrix_continuous K hζ s).mul continuous_const

end
end ArtinMatthews
