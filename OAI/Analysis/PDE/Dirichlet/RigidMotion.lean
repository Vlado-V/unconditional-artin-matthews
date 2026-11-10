module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Algebra.Quaternion
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The quaternionic infinitesimal rotation used in the mixed boundary
derivative estimate of `sections/dirichlet.tex`. -/

open scoped Matrix
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

abbrev Q := Quaternion ℝ

def quaternionPairing {ι : Type*} [Fintype ι] (x y : ι → Q) : Q :=
  ∑ i, star (x i) * y i

/-- Equation (dirichlet-rigid-motion), with the multiplication order retained. -/
def rigidMotionMatrix {ι : Type*} [Fintype ι] (ν v : ι → Q) : Matrix ι ι Q :=
  fun a b ↦ v a * star (ν b) - ν a * star (v b) -
    ν a * quaternionPairing ν v * star (ν b)

theorem star_quaternionPairing {ι : Type*} [Fintype ι] (x y : ι → Q) :
    star (quaternionPairing x y) = quaternionPairing y x := by
  simp [quaternionPairing, star_sum, star_mul]

theorem star_of_re_eq_zero (q : Q) (h : q.re = 0) : star q = -q := by
  ext <;> simp [h]

/-- Real orthogonality makes the infinitesimal matrix skew-Hermitian. -/
theorem rigidMotionMatrix_skew {ι : Type*} [Fintype ι] (ν v : ι → Q)
    (htangent : (quaternionPairing ν v).re = 0) :
    (rigidMotionMatrix ν v)ᴴ = -rigidMotionMatrix ν v := by
  have ha := star_of_re_eq_zero (quaternionPairing ν v) htangent
  apply Matrix.ext
  intro a b
  simp only [Matrix.conjTranspose_apply, rigidMotionMatrix, Matrix.neg_apply,
    star_sub, star_mul, star_star, ha]
  noncomm_ring

/-- Every real tangent vector is attained by an infinitesimal
quaternionic-unitary rotation of a unit normal. -/
theorem rigidMotionMatrix_normal {ι : Type*} [Fintype ι] (ν v : ι → Q)
    (hunit : quaternionPairing ν ν = 1)
    (htangent : (quaternionPairing ν v).re = 0) :
    rigidMotionMatrix ν v *ᵥ ν = v := by
  have ha := star_of_re_eq_zero (quaternionPairing ν v) htangent
  have hswap : quaternionPairing v ν = -quaternionPairing ν v := by
    rw [← star_quaternionPairing, ha]
  funext a
  simp only [Matrix.mulVec, dotProduct, rigidMotionMatrix, sub_mul,
    Finset.sum_sub_distrib, mul_assoc]
  simp only [← Finset.mul_sum]
  change v a * quaternionPairing ν ν -
    ν a * quaternionPairing v ν -
    ν a * (quaternionPairing ν v * quaternionPairing ν ν) = v a
  rw [hunit, hswap]
  noncomm_ring

end OAI.Analysis.PDE.Dirichlet
