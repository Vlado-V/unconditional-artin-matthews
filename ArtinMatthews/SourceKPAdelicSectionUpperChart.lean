module

public import ArtinMatthews.SourceKPArchTranslatedProfile
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

/-! Every actual adelic section has a smooth upper-half-space chart
at each complex place, with the exact positive Casimir eigenvalue. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix OAI.CubicEisenstein
open SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicSectionUpperChart (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (v : InfinitePlace K) (p : EuclideanSpatial) : ℂ :=
  if hp : 0 < p 2 then sourceKPAdelicCompactScalar K hζ s
    (q*sourceArchGroupSingle K hζ v
      (upperSection ((p 0 : ℂ)+(p 1 : ℂ)*Complex.I) (p 2) hp : GL (Fin 2) ℂ)) else 0

theorem sourceKPAdelicSectionUpperChart_factor (s : ℂ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ)
    (v : InfinitePlace K) :
    sourceKPAdelicSectionUpperChart K hζ s (ProjGenLinGroup.mk g,qf) v =
      fun p => sourceArchTranslatedSectionChart s
        (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) p *
          sourceArchOtherScalar K hζ s g qf v := by
  funext p
  unfold sourceKPAdelicSectionUpperChart sourceArchTranslatedSectionChart
  split_ifs with hp
  · exact sourceArchCompactScalar_single_right K hζ s g qf v _
  · rw [zero_mul]

theorem sourceKPAdelicSectionUpperChart_contDiffAt (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    ContDiffAt (ℝ) (∞ : ℕ∞ω) (sourceKPAdelicSectionUpperChart K hζ s q v) p := by
  obtain ⟨qArch,qf⟩ := q
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective qArch
  rw [sourceKPAdelicSectionUpperChart_factor]
  exact (sourceArchTranslatedSectionChart_contDiffAt s _ p hp).mul contDiffAt_const

theorem sourceKPAdelicSectionUpperChart_contDiffOn (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) :
    ContDiffOn (ℝ) (2 : ℕ∞ω) (sourceKPAdelicSectionUpperChart K hζ s q v)
      {p : EuclideanSpatial | 0 < p 2} := by
  intro p hp
  exact (sourceKPAdelicSectionUpperChart_contDiffAt K hζ s q v p hp).contDiffWithinAt.of_le (by simp)

private theorem sourceKPChart_laplacian_mul_const (f : EuclideanSpatial → ℂ) (c : ℂ)
    (hf : ∀ p : EuclideanSpatial, 0 < p 2 → ContDiffAt (ℝ) (∞ : ℕ∞ω) f p)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    positiveEuclideanLaplacian (fun x => f x*c) p = positiveEuclideanLaplacian f p*c := by
  have he : (fun x => f x*c) = fun x => c*f x := by funext x; exact mul_comm _ _
  rw [he, positiveEuclideanLaplacian_eq_axis _ (fun x hx => contDiffAt_const.mul (hf x hx)) p hp,
    axisLaplacian_const_mul, positiveEuclideanLaplacian_eq_axis f hf p hp]
  ring

theorem sourceKPAdelicSectionUpperChart_laplacian (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    positiveEuclideanLaplacian (sourceKPAdelicSectionUpperChart K hζ s q v) p =
      (1-4*s^2)*sourceKPAdelicSectionUpperChart K hζ s q v p := by
  obtain ⟨qArch,qf⟩ := q
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective qArch
  rw [sourceKPAdelicSectionUpperChart_factor,
    sourceKPChart_laplacian_mul_const _ _ (sourceArchTranslatedSectionChart_contDiffAt s _) p hp,
    sourceArchTranslatedSectionChart_laplacian s _ p hp]
  ring

end
end ArtinMatthews
