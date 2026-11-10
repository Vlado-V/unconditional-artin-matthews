module

public import ArtinMatthews.SourceHyperbolicEnergy
public import ArtinMatthews.SourceArchMobiusCoordinates
public import ArtinMatthews.SourceArchGradientIsometry
public import ArtinMatthews.SourceArchMobiusDifferential
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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

/-! The exact hyperbolic Dirichlet integrand under a genuine Mobius action. -/
namespace ArtinMatthews.SourceArchJacquet
open OAI.CubicEisenstein SourceHyperbolicGreen
open scoped BigOperators
noncomputable section

lemma sourceArch_coordinateVector_basis (j : Fin 3) :
    euclideanCoordinateVector j = EuclideanSpace.basisFun (Fin 3) ℝ j := by
  rw [EuclideanSpace.basisFun_apply]
  rfl

lemma sourceArch_similarity_gradientEnergy (A : EuclideanSpatial → EuclideanSpatial)
    (p : EuclideanSpatial) (r : ℝ) (e : EuclideanSpatial ≃ₗᵢ[ℝ] EuclideanSpatial)
    (hA : HasFDerivAt A (r • e.toContinuousLinearEquiv.toContinuousLinearMap) p)
    (hY : A p 2 = r * p 2) (f : EuclideanSpatial → ℂ)
    (hf : DifferentiableAt ℝ f (A p)) :
    gradientEnergy (f ∘ A) p = gradientEnergy f (A p) := by
  have hd := (hf.hasFDerivAt.comp p hA).fderiv
  unfold gradientEnergy coordinatePartial
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply]
  simp_rw [sourceArch_coordinateVector_basis]
  rw [sourceArch_scaled_orthonormal_gradient_square, hY]
  ring

theorem sourceArchMobiusEuclidean_gradientEnergy (g : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (f : EuclideanSpatial → ℂ) (p : EuclideanSpatial) (hp : 0 < p 2)
    (hf : DifferentiableAt ℝ f (sourceArchMobiusEuclidean g p)) :
    gradientEnergy (f ∘ sourceArchMobiusEuclidean g) p =
      gradientEnergy f (sourceArchMobiusEuclidean g p) := by
  obtain ⟨r, e, _hr, hD, hY⟩ := sourceArchMobiusEuclidean_isometric_differential g p hp
  exact sourceArch_similarity_gradientEnergy _ p r e hD hY f hf

end
end ArtinMatthews.SourceArchJacquet
