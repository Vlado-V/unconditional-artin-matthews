module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
public import OAI.RepresentationTheory.Theta.Adelic.GaussianSchwartz
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! # Vacuum -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Vacuum.CM

noncomputable section

/-! Construct PoissonAutomorphy's standard real Gaussian vacuum directly as a
Schwartz function. Its existence is independent of any Weil data. -/

open scoped Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

variable (I : Type*) [Fintype I]

def exponent (x : EuclideanSpace ℝ I) : ℂ := -∑ i, (x i : ℂ) ^ 2

theorem exponent_temperate : Function.HasTemperateGrowth (exponent I) := by
  have hc (i : I) : Function.HasTemperateGrowth (fun x : EuclideanSpace ℝ I => (x i : ℂ)) :=
    (Complex.ofRealCLM.comp ((ContinuousLinearMap.proj i : (I → ℝ) →L[ℝ] ℝ).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).toContinuousLinearMap)).hasTemperateGrowth
  exact (Function.HasTemperateGrowth.sum (fun i _ => (hc i).pow 2)).neg

theorem exponent_real (x : EuclideanSpace ℝ I) : (exponent I x).re = -‖x‖ ^ 2 := by
  simp only [exponent, ← Complex.ofReal_pow, Complex.neg_re, Complex.re_sum,
    Complex.ofReal_re, EuclideanSpace.real_norm_sq_eq]

def euclideanGaussian : SchwartzMap (EuclideanSpace ℝ I) ℂ :=
  RepresentationTheory.Theta.Adelic.GaussianSchwartz.gaussianOfExponent (exponent I)
    (exponent_temperate I) (exponent_real I)

def gaussianCoordinates : (I → ℝ) ≃L[ℝ] EuclideanSpace ℝ I :=
  ((LinearEquiv.smulOfNeZero ℝ (I → ℝ) (Real.sqrt Real.pi)
    (Real.sqrt_pos.mpr Real.pi_pos).ne').toContinuousLinearEquiv).trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).symm

def gaussian : SchwartzMap (I → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (gaussianCoordinates I) (euclideanGaussian I)

theorem gaussian_apply (x : I → ℝ) :
    gaussian I x = Complex.exp (-((Real.pi : ℂ) * ∑ i, (x i : ℂ) ^ 2)) := by
  change Complex.exp (-∑ i, (((Real.sqrt Real.pi) * x i : ℝ) : ℂ) ^ 2) = _
  congr 1
  simp only [Complex.ofReal_mul, mul_pow, ← Finset.mul_sum,
    ← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]

def vacuum : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I :=
  ⟨gaussian I, Submodule.subset_span ⟨gaussian I, rfl⟩⟩

theorem vacuum_apply (x : I → ℝ) :
    (vacuum I).val x = Complex.exp (-((Real.pi : ℂ) * ∑ i, (x i : ℂ) ^ 2)) :=
  gaussian_apply I x

theorem vacuum_zero : (vacuum I).val 0 = 1 := by
  simp only [vacuum_apply, Pi.zero_apply, Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, mul_zero, neg_zero, Complex.exp_zero]

theorem vacuum_ne_zero : vacuum I ≠ 0 := by
  intro h
  have he := congrArg (fun f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I => f.val 0) h
  rw [vacuum_zero] at he
  exact one_ne_zero he

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Vacuum.CM
