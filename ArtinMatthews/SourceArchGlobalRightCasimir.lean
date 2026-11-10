module

public import ArtinMatthews.SourceArchRightCasimir
public import ArtinMatthews.SourceArchSphericalRightCasimir
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

theorem sourceArchGlobalCasimir_compactScalar (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) :
    sourceArchGlobalCasimir K hζ (sourceKPAdelicCompactScalar K hζ s) q v =
      (1-4*s^2)*sourceKPAdelicCompactScalar K hζ s q := by
  rcases q with ⟨qI,qf⟩
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective qI
  let a := sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)
  let c := sourceArchOtherScalar K hζ s g qf v
  have hU (z : ℂ) : sourceArchGlobalUpperTranslate K hζ (sourceKPAdelicCompactScalar K hζ s)
      (ProjGenLinGroup.mk g,qf) v z = fun t => sourceArchUpperSection s a z t*c := by
    rw [sourceArchGlobalUpperTranslate_compactScalar]
    exact funext (sourceArchGlobalUpperSection_factor K hζ s g qf v z)
  have hA : sourceArchGlobalDiagonalTranslate K hζ (sourceKPAdelicCompactScalar K hζ s)
      (ProjGenLinGroup.mk g,qf) v = fun t => sourceArchDiagonalSection s a t*c := by
    rw [sourceArchGlobalDiagonalTranslate_compactScalar]
    exact funext (sourceArchGlobalDiagonalSection_factor K hζ s g qf v)
  have hU2 (z : ℂ) : deriv (deriv (sourceArchGlobalUpperTranslate K hζ
      (sourceKPAdelicCompactScalar K hζ s) (ProjGenLinGroup.mk g,qf) v z)) 0 =
        deriv (deriv (sourceArchUpperSection s a z)) 0*c := by
    have hd : deriv (sourceArchGlobalUpperTranslate K hζ (sourceKPAdelicCompactScalar K hζ s)
        (ProjGenLinGroup.mk g,qf) v z) = fun t => sourceArchUpperSectionOne s a z t*c := by
      rw [hU]
      funext t
      exact ((sourceArchUpperSection_hasDerivAt s a z t).mul_const c).deriv
    rw [hd, sourceArchUpperSection_deriv_two]
    exact ((sourceArchUpperSectionOne_hasDerivAt s a z 0).mul_const c).deriv
  have hA1 : deriv (sourceArchGlobalDiagonalTranslate K hζ (sourceKPAdelicCompactScalar K hζ s)
      (ProjGenLinGroup.mk g,qf) v) = fun t => sourceArchDiagonalSectionOne s a t*c := by
    rw [hA]
    funext t
    exact ((sourceArchDiagonalSection_hasDerivAt s a t).mul_const c).deriv
  have hA2 : deriv (deriv (sourceArchGlobalDiagonalTranslate K hζ
      (sourceKPAdelicCompactScalar K hζ s) (ProjGenLinGroup.mk g,qf) v)) 0 =
        deriv (deriv (sourceArchDiagonalSection s a)) 0*c := by
    rw [hA1, sourceArchDiagonalSection_deriv_two]
    exact ((sourceArchDiagonalSectionOne_hasDerivAt s a 0).mul_const c).deriv
  rw [sourceArchGlobalCasimir, hU2, hU2, hA2, hA1]
  dsimp only
  rw [← sourceArchDiagonalSection_deriv s a 0]
  calc
    _ = sourceArchSphericalRightCasimir s a*c := by
      unfold sourceArchSphericalRightCasimir
      ring
    _ = (1-4*s^2)*sourceArchSphericalGL s a*c := by rw [sourceArchSphericalRightCasimir_eq]
    _ = _ := by
      rw [sourceArchCompactScalar_single_base K hζ s g qf v]
      ring

end
end ArtinMatthews
