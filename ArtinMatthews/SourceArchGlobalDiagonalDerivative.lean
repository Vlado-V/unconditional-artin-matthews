module

public import ArtinMatthews.SourceArchSingleRightAction
public import ArtinMatthews.SourceArchDiagonalDerivative
public import ArtinMatthews.SourceArchDiagonalCompact
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

def sourceArchGlobalDiagonalSection (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (v : InfinitePlace K) (t : ℝ) : ℂ :=
  sourceKPAdelicCompactScalar K hζ s
    (q * sourceArchGroupSingle K hζ v (sourceArchPositiveDiagonal t))

theorem sourceArchGlobalDiagonalSection_factor (s : ℂ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ)
    (v : InfinitePlace K) (t : ℝ) :
    sourceArchGlobalDiagonalSection K hζ s (ProjGenLinGroup.mk g,qf) v t =
      sourceArchDiagonalSection s (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) t *
        sourceArchOtherScalar K hζ s g qf v :=
  sourceArchCompactScalar_single_right K hζ s g qf v (sourceArchPositiveDiagonal t)

theorem sourceArchGlobalDiagonalSection_twice_differentiable (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) :
    Differentiable ℝ (sourceArchGlobalDiagonalSection K hζ s q v) ∧
      Differentiable ℝ (deriv (sourceArchGlobalDiagonalSection K hζ s q v)) := by
  rcases q with ⟨qI,qf⟩
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective qI
  let a := sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)
  let c := sourceArchOtherScalar K hζ s g qf v
  have he : sourceArchGlobalDiagonalSection K hζ s (ProjGenLinGroup.mk g,qf) v =
      fun t => sourceArchDiagonalSection s a t * c :=
    funext (sourceArchGlobalDiagonalSection_factor K hζ s g qf v)
  have hd : deriv (sourceArchGlobalDiagonalSection K hζ s (ProjGenLinGroup.mk g,qf) v) =
      fun t => sourceArchDiagonalSectionOne s a t * c := by
    rw [he]
    funext t
    exact ((sourceArchDiagonalSection_hasDerivAt s a t).mul_const c).deriv
  constructor
  · rw [he]
    exact fun t => ((sourceArchDiagonalSection_hasDerivAt s a t).mul_const c).differentiableAt
  · rw [hd]
    exact fun t => ((sourceArchDiagonalSectionOne_hasDerivAt s a t).mul_const c).differentiableAt

theorem sourceArchGlobalDiagonalSection_derivative_bounds (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K)
    {R t B : ℝ} (ht : |t| ≤ R) (hs : |(2*s+1).re| ≤ B) :
    ‖deriv (sourceArchGlobalDiagonalSection K hζ s q v) t‖ ≤
        Real.exp (B*R) * ‖2*s+1‖ *
          ‖sourceKPAdelicCompactScalar K hζ s q‖ ∧
    ‖deriv (deriv (sourceArchGlobalDiagonalSection K hζ s q v)) t‖ ≤
        Real.exp (B*R) * (‖2*s+1‖^2+‖2*s+1‖) *
          ‖sourceKPAdelicCompactScalar K hζ s q‖ := by
  rcases q with ⟨qI,qf⟩
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective qI
  let a := sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)
  let c := sourceArchOtherScalar K hζ s g qf v
  have he : sourceArchGlobalDiagonalSection K hζ s (ProjGenLinGroup.mk g,qf) v =
      fun x => sourceArchDiagonalSection s a x * c :=
    funext (sourceArchGlobalDiagonalSection_factor K hζ s g qf v)
  have hd : deriv (sourceArchGlobalDiagonalSection K hζ s (ProjGenLinGroup.mk g,qf) v) =
      fun x => sourceArchDiagonalSectionOne s a x * c := by
    rw [he]
    funext x
    exact ((sourceArchDiagonalSection_hasDerivAt s a x).mul_const c).deriv
  have hdd : deriv (deriv (sourceArchGlobalDiagonalSection K hζ s (ProjGenLinGroup.mk g,qf) v)) =
      fun x => sourceArchDiagonalSectionTwo s a x * c := by
    rw [hd]
    funext x
    exact ((sourceArchDiagonalSectionOne_hasDerivAt s a x).mul_const c).deriv
  have hb : ‖sourceKPAdelicCompactScalar K hζ s (ProjGenLinGroup.mk g,qf)‖ =
      (sourceArchHeight a)^((2*s+1).re) * ‖c‖ := by
    rw [sourceArchCompactScalar_single_base K hζ s g qf v, norm_mul]
    rw [sourceArchSphericalGL, Complex.norm_cpow_eq_rpow_re_of_pos (sourceArchHeight_pos _)]
  constructor
  · rw [hd, norm_mul]
    have h := sourceArchDiagonalSection_deriv_compact_bound s a ht hs
    rw [sourceArchDiagonalSection_deriv] at h
    calc
      _ ≤ (Real.exp (B*R) * ‖2*s+1‖ *
          (sourceArchHeight a)^((2*s+1).re)) * ‖c‖ := mul_le_mul_of_nonneg_right h (norm_nonneg c)
      _ = _ := by rw [hb]; ring
  · rw [hdd, norm_mul]
    have h := sourceArchDiagonalSection_deriv_two_compact_bound s a ht hs
    rw [sourceArchDiagonalSection_deriv_two] at h
    calc
      _ ≤ (Real.exp (B*R) * (‖2*s+1‖^2+‖2*s+1‖) *
          (sourceArchHeight a)^((2*s+1).re)) * ‖c‖ := mul_le_mul_of_nonneg_right h (norm_nonneg c)
      _ = _ := by rw [hb]; ring

end
end ArtinMatthews
