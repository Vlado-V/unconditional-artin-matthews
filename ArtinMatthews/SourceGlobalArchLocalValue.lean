module

public import ArtinMatthews.SourceArchSectionFactorization
public import ArtinMatthews.SourceArchCompletedJacquet
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

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceArchSphericalProduct_single (s : ℂ) (v : InfinitePlace K)
    (hv : InfinitePlace.IsComplex v) (g : PGL(2, v.Completion)) :
    sourceArchSphericalProduct K hζ s (sourceArchSinglePGL K v g) =
      sourceArchCompletedSphericalSection K v hv s g := by
  classical
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective g
  rw [sourceArchSinglePGL_mk, sourceArchSphericalProduct_mk]
  rw [Finset.prod_eq_single v]
  · rw [sourceArchGLPiEquiv_single, Pi.mulSingle_eq_same]
    unfold sourceArchCompletedSphericalSection
    rw [ProjGenLinGroup.map_mk, sourceArchSphericalSection_mk]
    congr 1
  · intro w _ hw
    rw [sourceArchGLPiEquiv_single, Pi.mulSingle_eq_of_ne hw, map_one]
    simpa only [← sourceArchSphericalSection_mk, map_one] using sourceArchSphericalSection_one s
  · simp

theorem sourceGlobalArchLocal_scalar (s : ℂ) (v : InfinitePlace K)
    (hv : InfinitePlace.IsComplex v) (g : PGL(2, v.Completion))
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPAdelicCompactScalar K hζ s (sourceArchSinglePGL K v g,qf) =
      sourceArchCompletedSphericalSection K v hv s g *
        sourceKPAdelicCompactScalar K hζ s (1,qf) := by
  rw [sourceArchCompactScalar_factor, sourceArchSphericalProduct_single K hζ s v hv]

theorem sourceGlobalArchLocal_embedded_scalar (s : ℂ) (v : InfinitePlace K)
    (hv : InfinitePlace.IsComplex v) (g : PGL(2, v.Completion))
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPAdelicCompactScalar K hζ s (sourceArchLocalToAdelic K hζ v g * (1,qf)) =
      sourceArchCompletedSphericalSection K v hv s g *
        sourceKPAdelicCompactScalar K hζ s (1,qf) := by
  simpa only [sourceArchLocalToAdelic_apply, Prod.mk_mul_mk, mul_one, one_mul] using
    sourceGlobalArchLocal_scalar K hζ s v hv g qf

end
end ArtinMatthews
