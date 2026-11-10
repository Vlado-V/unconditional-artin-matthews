module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import OAI.RepresentationTheory.Weil.Local.RealDiagonalFresnel


set_option backward.privateInPublic true
@[expose] public section

/-! # Quadratic Norm Reflection -/

namespace OAI.RepresentationTheory.Weil.Local.QuadraticNormReflection.Construction

noncomputable section

/-! A symmetric change of two coordinates scales x²+y² by a nonzero quadratic norm. -/

open _root_.Matrix

variable {k : Type} [Field k]

def quadraticNormReflection (s t : k) : Matrix (Fin 2) (Fin 2) k := !![s, t; t, -s]

theorem quadraticNormReflection_isSymm (s t : k) : (quadraticNormReflection s t).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem quadraticNormReflection_square (s t : k) :
    quadraticNormReflection s t * quadraticNormReflection s t = (s ^ 2 + t ^ 2) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quadraticNormReflection, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def quadraticNormGeneralLinear (s t : k) (h : s ^ 2 + t ^ 2 ≠ 0) : FunctionsMetaplectic.Construction.GeneralLinear k 2 where
  val := quadraticNormReflection s t
  inv := (s ^ 2 + t ^ 2)⁻¹ • quadraticNormReflection s t
  val_inv := by
    rw [mul_smul_comm, quadraticNormReflection_square, smul_smul, inv_mul_cancel₀ h, one_smul]
  inv_val := by
    rw [smul_mul_assoc, quadraticNormReflection_square, smul_smul, inv_mul_cancel₀ h, one_smul]

theorem quadratic_pair_constant (c : k) (x : FunctionsMetaplectic.Construction.Position k 2) :
    FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => c) x = c * (x 0 ^ 2 + x 1 ^ 2) / 2 := by
  rw [RealDiagonalFresnel.Construction.quadratic_diagonal]
  simp only [Fin.sum_univ_two]
  ring

theorem quadratic_normReflection (s t c : k) (x : FunctionsMetaplectic.Construction.Position k 2) :
    FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => c) (quadraticNormReflection s t *ᵥ x) =
      FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => c * (s ^ 2 + t ^ 2)) x := by
  rw [quadratic_pair_constant, quadratic_pair_constant]
  simp [quadraticNormReflection, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem quadratic_normGeneralLinear_inverse (s t c : k) (h : s ^ 2 + t ^ 2 ≠ 0)
    (x : FunctionsMetaplectic.Construction.Position k 2) :
    FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => c) ((quadraticNormGeneralLinear s t h)⁻¹.val *ᵥ x) =
      FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => c / (s ^ 2 + t ^ 2)) x := by
  rw [quadratic_pair_constant, quadratic_pair_constant]
  change c * (((((s ^ 2 + t ^ 2)⁻¹ • quadraticNormReflection s t) *ᵥ x) 0) ^ 2 +
    ((((s ^ 2 + t ^ 2)⁻¹ • quadraticNormReflection s t) *ᵥ x) 1) ^ 2) / 2 = _
  simp [quadraticNormReflection, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  field_simp
  ring

end

end OAI.RepresentationTheory.Weil.Local.QuadraticNormReflection.Construction
