module

public import ArtinMatthews.SourceKPAdelicConstantTermPeriodization
public import ArtinMatthews.SourceArchSectionFactorization
public import ArtinMatthews.SourceArchSectionContinuity
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
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

theorem sourceKPUpperMatrix_continuous (R : Type*) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] : Continuous (sourceKPUpperMatrix R) := by
  have he : sourceKPUpperMatrix R = GeneralLinearGroup.upperRightHom := by
    funext x
    apply GeneralLinearGroup.ext
    intro i j
    rfl
  rw [he]
  exact GeneralLinearGroup.continuous_upperRightHom

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceArchSphericalProduct_openCell_continuous (s : ℂ)
    (g : PGL(2, InfiniteAdeleRing K)) :
    Continuous (fun x : InfiniteAdeleRing K => sourceArchSphericalProduct K hζ s
      (ProjGenLinGroup.mk (sourceKPWeylMatrix (InfiniteAdeleRing K)) *
        ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) x) * g)) := by
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective g
  simp_rw [← map_mul]
  exact (sourceArchSphericalProduct_matrix_continuous K hζ s).comp
    ((continuous_const.mul (sourceKPUpperMatrix_continuous (InfiniteAdeleRing K))).mul continuous_const)

theorem sourceArchOpenCell_continuous (s : ℂ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun x : InfiniteAdeleRing K => sourceKPAdelicCompactScalar K hζ s
      (ProjGenLinGroup.mk (sourceKPWeylMatrix (InfiniteAdeleRing K) *
        sourceKPUpperMatrix (InfiniteAdeleRing K) x * g),qf)) :=
  (sourceArchCompactScalar_continuous K hζ s qf).comp
    ((continuous_const.mul (sourceKPUpperMatrix_continuous (InfiniteAdeleRing K))).mul continuous_const)

theorem sourceKPAdelicIntertwiningKernel_arch_continuous (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (yf : 𝔸ᶠ[K]) :
    Continuous (fun x : InfiniteAdeleRing K => sourceKPAdelicIntertwiningKernel K hζ s g (x,yf)) := by
  obtain ⟨gI,hgI⟩ := ProjGenLinGroup.mk_surjective g.1
  let qf := (sourceKPAdelicProjectiveWeyl K hζ).2 * sourceKPFiniteAdeleUpperLift K hζ yf * g.2
  have hw : (sourceKPAdelicProjectiveWeyl K hζ).1 =
      ProjGenLinGroup.mk (sourceKPWeylMatrix (InfiniteAdeleRing K)) := by
    change ProjGenLinGroup.map (algebraMap K (InfiniteAdeleRing K))
      (ProjGenLinGroup.mk (sourceKPWeylMatrix K)) = _
    rw [ProjGenLinGroup.map_mk, sourceKPWeylMatrix_map]
  have he (x : InfiniteAdeleRing K) :
      sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ (x,yf) * g =
        (ProjGenLinGroup.mk (sourceKPWeylMatrix (InfiniteAdeleRing K) *
          sourceKPUpperMatrix (InfiniteAdeleRing K) x * gI),qf) := by
    apply Prod.ext
    · simp only [Prod.fst_mul, hw]
      change (ProjGenLinGroup.mk (sourceKPWeylMatrix (InfiniteAdeleRing K)) *
        ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) x)) * g.1 = _
      rw [← hgI, map_mul, map_mul]
    · rfl
  simp_rw [sourceKPAdelicIntertwiningKernel, he]
  exact sourceArchOpenCell_continuous K hζ s gI qf

end
end ArtinMatthews
