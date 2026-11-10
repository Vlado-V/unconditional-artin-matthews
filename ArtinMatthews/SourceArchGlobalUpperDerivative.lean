module

public import ArtinMatthews.SourceArchUpperCompact
public import ArtinMatthews.SourceArchSingleRightAction
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
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceArchGlobalUpperSection (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (v : InfinitePlace K) (z : ℂ) (t : ℝ) : ℂ :=
  sourceKPAdelicCompactScalar K hζ s
    (q * sourceArchGroupSingle K hζ v (sourceKPUpperMatrix ℂ ((t : ℂ)*z)))

theorem sourceArchGlobalUpperSection_factor (s : ℂ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ)
    (v : InfinitePlace K) (z : ℂ) (t : ℝ) :
    sourceArchGlobalUpperSection K hζ s (ProjGenLinGroup.mk g,qf) v z t =
      sourceArchUpperSection s (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) z t *
        sourceArchOtherScalar K hζ s g qf v :=
  sourceArchCompactScalar_single_right K hζ s g qf v (sourceKPUpperMatrix ℂ ((t : ℂ)*z))

theorem sourceArchGlobalUpperSection_twice_differentiable (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) (z : ℂ) :
    Differentiable ℝ (sourceArchGlobalUpperSection K hζ s q v z) ∧
      Differentiable ℝ (deriv (sourceArchGlobalUpperSection K hζ s q v z)) := by
  rcases q with ⟨qI,qf⟩
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective qI
  let a := sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)
  let c := sourceArchOtherScalar K hζ s g qf v
  have he : sourceArchGlobalUpperSection K hζ s (ProjGenLinGroup.mk g,qf) v z =
      fun t => sourceArchUpperSection s a z t * c :=
    funext (sourceArchGlobalUpperSection_factor K hζ s g qf v z)
  have hd : deriv (sourceArchGlobalUpperSection K hζ s (ProjGenLinGroup.mk g,qf) v z) =
      fun t => sourceArchUpperSectionOne s a z t * c := by
    rw [he]
    funext t
    exact ((sourceArchUpperSection_hasDerivAt s a z t).mul_const c).deriv
  constructor
  · rw [he]
    exact fun t => ((sourceArchUpperSection_hasDerivAt s a z t).mul_const c).differentiableAt
  · rw [hd]
    exact fun t => ((sourceArchUpperSectionOne_hasDerivAt s a z t).mul_const c).differentiableAt

theorem sourceArchGlobalUpperSection_derivative_bounds (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) (z : ℂ)
    {R t B : ℝ} (ht : |t| ≤ R) (hs : |(2*s+1).re| ≤ B) :
    ‖deriv (sourceArchGlobalUpperSection K hζ s q v z) t‖ ≤
        (sourceArchUpperCompactConstant R z)^B * ‖2*s+1‖ * ‖z‖ *
          ‖sourceKPAdelicCompactScalar K hζ s q‖ ∧
    ‖deriv (deriv (sourceArchGlobalUpperSection K hζ s q v z)) t‖ ≤
        (sourceArchUpperCompactConstant R z)^B * (‖2*s+1‖^2+3*‖2*s+1‖) * ‖z‖^2 *
          ‖sourceKPAdelicCompactScalar K hζ s q‖ := by
  rcases q with ⟨qI,qf⟩
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective qI
  let a := sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)
  let c := sourceArchOtherScalar K hζ s g qf v
  have he : sourceArchGlobalUpperSection K hζ s (ProjGenLinGroup.mk g,qf) v z =
      fun x => sourceArchUpperSection s a z x * c :=
    funext (sourceArchGlobalUpperSection_factor K hζ s g qf v z)
  have hd : deriv (sourceArchGlobalUpperSection K hζ s (ProjGenLinGroup.mk g,qf) v z) =
      fun x => sourceArchUpperSectionOne s a z x * c := by
    rw [he]
    funext x
    exact ((sourceArchUpperSection_hasDerivAt s a z x).mul_const c).deriv
  have hdd : deriv (deriv (sourceArchGlobalUpperSection K hζ s (ProjGenLinGroup.mk g,qf) v z)) =
      fun x => sourceArchUpperSectionTwo s a z x * c := by
    rw [hd]
    funext x
    exact ((sourceArchUpperSectionOne_hasDerivAt s a z x).mul_const c).deriv
  have hb : ‖sourceKPAdelicCompactScalar K hζ s (ProjGenLinGroup.mk g,qf)‖ =
      (sourceArchHeight a)^((2*s+1).re) * ‖c‖ := by
    rw [sourceArchCompactScalar_single_base K hζ s g qf v, norm_mul]
    rw [sourceArchSphericalGL, Complex.norm_cpow_eq_rpow_re_of_pos (sourceArchHeight_pos _)]
  constructor
  · rw [hd, norm_mul]
    have h := sourceArchUpperSection_deriv_compact_bound s a z ht hs
    rw [sourceArchUpperSection_deriv] at h
    calc
      _ ≤ ((sourceArchUpperCompactConstant R z)^B * ‖2*s+1‖ * ‖z‖ *
          (sourceArchHeight a)^((2*s+1).re)) * ‖c‖ := mul_le_mul_of_nonneg_right h (norm_nonneg c)
      _ = _ := by rw [hb]; ring
  · rw [hdd, norm_mul]
    have h := sourceArchUpperSection_deriv_two_compact_bound s a z ht hs
    rw [sourceArchUpperSection_deriv_two] at h
    calc
      _ ≤ ((sourceArchUpperCompactConstant R z)^B * (‖2*s+1‖^2+3*‖2*s+1‖) * ‖z‖^2 *
          (sourceArchHeight a)^((2*s+1).re)) * ‖c‖ := mul_le_mul_of_nonneg_right h (norm_nonneg c)
      _ = _ := by rw [hb]; ring

end
end ArtinMatthews
