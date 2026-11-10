module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.TransposeSubstitution
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
public import OAI.RepresentationTheory.Weil.Local.DiagonalAlgebra


set_option backward.privateInPublic true
@[expose] public section

/-! # Quadratic Diagonal Data -/

namespace OAI.RepresentationTheory.Weil.Local.QuadraticDiagonalData.Construction

noncomputable section

/-! Quadratic identities and inverse matrices for a chosen congruence diagonalization. -/

open _root_.Matrix

variable {k : Type} [Field k] {n : ℕ}

theorem congruence_diagonal_inverse (M A : FunctionsMetaplectic.Construction.GeneralLinear k n) (a : Fin n → kˣ)
    (h : A.val.transpose * M.val * A.val = diagonal (fun i => (a i).val)) :
    M⁻¹.val = A.val * diagonal (fun i => (a i).val⁻¹) * A.val.transpose := by
  have he : TransposeSubstitution.Construction.transposeGeneralLinear A * M * A = DiagonalAlgebra.Construction.diagonalGeneralLinear a := Units.ext h
  have hi : M⁻¹ = A * (DiagonalAlgebra.Construction.diagonalGeneralLinear a)⁻¹ * TransposeSubstitution.Construction.transposeGeneralLinear A := by
    rw [← he]
    group
  have hv := congrArg Units.val hi
  rw [DiagonalAlgebra.Construction.diagonalGeneralLinear_inv] at hv
  simpa only [Units.val_mul, DiagonalAlgebra.Construction.diagonalGeneralLinear, TransposeSubstitution.Construction.transposeGeneralLinear, Units.val_inv_eq_inv_val] using hv

theorem quadratic_diagonal_inverse_coordinates (M A : FunctionsMetaplectic.Construction.GeneralLinear k n) (a : Fin n → kˣ)
    (h : A.val.transpose * M.val * A.val = diagonal (fun i => (a i).val)) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) (A⁻¹.val *ᵥ x) = FunctionsMetaplectic.Construction.quadratic M.val x := by
  rw [← h, TransposeSubstitution.Construction.quadratic_matrix_congruence, Matrix.mulVec_mulVec, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, one_mulVec]

theorem quadratic_inverse_diagonal_coordinates (M A : FunctionsMetaplectic.Construction.GeneralLinear k n) (a : Fin n → kˣ)
    (h : A.val.transpose * M.val * A.val = diagonal (fun i => (a i).val)) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) (A.val.transpose *ᵥ x) = FunctionsMetaplectic.Construction.quadratic M⁻¹.val x := by
  rw [congruence_diagonal_inverse M A a h, ← TransposeSubstitution.Construction.quadratic_matrix_congruence, Matrix.transpose_transpose]

end

end OAI.RepresentationTheory.Weil.Local.QuadraticDiagonalData.Construction
