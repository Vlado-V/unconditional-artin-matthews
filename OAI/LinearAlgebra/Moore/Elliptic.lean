module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import OAI.LinearAlgebra.Moore.Derivative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
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
public import OAI.LinearAlgebra.Moore.Inverse
public import OAI.LinearAlgebra.Moore.Normalize


set_option backward.privateInPublic true
@[expose] public section

/-! Positivity of the Moore linearization through the faithful representation. -/

namespace OAI.LinearAlgebra.Moore

open Matrix
open scoped MatrixOrder ComplexOrder

theorem isHermitian_of_complexify {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : (complexify A).IsHermitian) : A.IsHermitian := by
  apply complexify_injective
  rw [complexify_star]
  exact hA

theorem complex_trace_mul_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [star_eq_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  exact (Complex.nonneg_iff.mp (hA.mul_mul_conjTranspose_same C).trace_nonneg).1

/-- An actual quaternionic inverse remains positive definite in the faithful
complex representation. -/
theorem complexify_inverse_posDef (n : ℕ)
    (A C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosDef) (hAC : A * C = 1) :
    (complexify C).PosDef := by
  have h : complexify A * complexify C = 1 := by
    rw [← complexify_mul, hAC, complexify_one]
  rw [← Matrix.inv_eq_right_inv h]
  exact hA.inv

/-- Ellipticity of the inverse-trace linearization at matrices with positive
Moore determinant. Positive semidefinite directions have nonnegative derivative. -/
theorem mooreDifferential_nonneg (n : ℕ)
    (A D C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosDef) (hD : (complexify D).PosSemidef)
    (hAC : A * C = 1) (hCA : C * A = 1) (hdet : 0 ≤ mooreDet n A) :
    0 ≤ mooreDifferential n A D := by
  rw [mooreDifferential_inverse n A D C (isHermitian_of_complexify hA.isHermitian)
    (isHermitian_of_complexify hD.isHermitian) hAC hCA]
  apply mul_nonneg hdet
  have hC := (complexify_inverse_posDef n A C hA hAC).posSemidef
  have h := complex_trace_mul_nonneg hC hD
  rw [← complexify_mul, complexify_trace_real] at h
  linarith

end OAI.LinearAlgebra.Moore
