module

public import ArtinMatthews.SourceArchGlobalUpperDerivative
public import ArtinMatthews.SourceArchGlobalDiagonalDerivative
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

def sourceArchGlobalUpperTranslate (f : SourceKPAdelicProjective K hζ → ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) (z : ℂ) (t : ℝ) : ℂ :=
  f (q * sourceArchGroupSingle K hζ v (sourceKPUpperMatrix ℂ ((t : ℂ)*z)))

def sourceArchGlobalDiagonalTranslate (f : SourceKPAdelicProjective K hζ → ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) (t : ℝ) : ℂ :=
  f (q * sourceArchGroupSingle K hζ v (sourceArchPositiveDiagonal t))

def sourceArchGlobalCasimir (f : SourceKPAdelicProjective K hζ → ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) : ℂ :=
  -(deriv (deriv (sourceArchGlobalUpperTranslate K hζ f q v 1)) 0 +
    deriv (deriv (sourceArchGlobalUpperTranslate K hζ f q v Complex.I)) 0 +
    deriv (deriv (sourceArchGlobalDiagonalTranslate K hζ f q v)) 0 -
    2 * deriv (sourceArchGlobalDiagonalTranslate K hζ f q v) 0)

theorem sourceArchGlobalUpperTranslate_compactScalar (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) (z : ℂ) :
    sourceArchGlobalUpperTranslate K hζ (sourceKPAdelicCompactScalar K hζ s) q v z =
      sourceArchGlobalUpperSection K hζ s q v z := rfl

theorem sourceArchGlobalDiagonalTranslate_compactScalar (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) :
    sourceArchGlobalDiagonalTranslate K hζ (sourceKPAdelicCompactScalar K hζ s) q v =
      sourceArchGlobalDiagonalSection K hζ s q v := rfl

end
end ArtinMatthews
