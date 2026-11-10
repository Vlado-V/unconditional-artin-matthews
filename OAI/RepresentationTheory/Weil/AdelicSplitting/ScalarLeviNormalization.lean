module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.DeterminantMeasure
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
public import Mathlib.Topology.Sheaves.Init
public import OAI.RepresentationTheory.Weil.Local.QuadraticIntertwiner


set_option backward.privateInPublic true
@[expose] public section

/-! # Scalar Levi Normalization -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ScalarLeviNormalization.LocalAnalysis

noncomputable section

section

/-! Algebraic rescaling identities for scalar quadratic phases. -/

open OAI.RepresentationTheory.Weil.Local.QuadraticIntertwiner.Construction

variable {k : Type} [Field k] (N : ℕ) (ψ : AddChar k ℂ) (b : k)

theorem quadraticOperator_mulShift_one (f : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) :
    Local.FunctionsMetaplectic.Construction.quadraticOperator (ψ.mulShift b) 1 f = Local.FunctionsMetaplectic.Construction.quadraticOperator ψ (b • 1) f := by
  funext x
  simp only [Local.FunctionsMetaplectic.Construction.quadraticOperator_apply, Local.QuadraticIntertwiner.Construction.quadratic_smul_matrix]
  rfl

theorem quadraticOperator_mulShift_neg_scaled (hb : b ≠ 0) (f : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) :
    Local.FunctionsMetaplectic.Construction.quadraticOperator (ψ.mulShift b) (-1) (fun y => f (b • y)) =
      fun y => Local.FunctionsMetaplectic.Construction.quadraticOperator ψ ((-b⁻¹) • 1) f (b • y) := by
  funext y
  simp only [Local.FunctionsMetaplectic.Construction.quadraticOperator_apply, Local.FunctionsMetaplectic.Construction.quadratic_neg, Local.QuadraticIntertwiner.Construction.quadratic_smul_matrix, Local.QuadraticIntertwiner.Construction.quadratic_smul_vector]
  change ψ (b * -Local.FunctionsMetaplectic.Construction.quadratic 1 y) * f (b • y) = ψ (b ^ 2 * ((-b⁻¹) * Local.FunctionsMetaplectic.Construction.quadratic 1 y)) * f (b • y)
  congr 2
  field_simp

theorem mulShift_negative_quadratic_scaled (hb : b ≠ 0) (x : Local.FunctionsMetaplectic.Construction.Position k N) :
    (ψ.mulShift b) (-Local.FunctionsMetaplectic.Construction.quadratic 1 (b⁻¹ • x)) = ψ (Local.FunctionsMetaplectic.Construction.quadratic ((-b⁻¹) • 1) x) := by
  rw [Local.QuadraticIntertwiner.Construction.quadratic_smul_vector, Local.QuadraticIntertwiner.Construction.quadratic_smul_matrix]
  change ψ (b * -(b⁻¹ ^ 2 * Local.FunctionsMetaplectic.Construction.quadratic 1 x)) = ψ ((-b⁻¹) * Local.FunctionsMetaplectic.Construction.quadratic 1 x)
  congr 1
  field_simp

end

/-! The normalized scalar Levi operator has exactly the positive
coefficient and substitution occurring in weighted Fresnel summation. -/

open scoped Classical

open OAI.RepresentationTheory.Weil.Local.QuadraticIntertwiner.Construction

def scalarLinearMatrix {k : Type} [Field k] (N : ℕ) (b : k) (hb : b ≠ 0) : Local.FunctionsMetaplectic.Construction.GeneralLinear k N :=
  Matrix.GeneralLinearGroup.scalar (Fin N) (Units.mk0 b hb)

theorem scalarLinearMatrix_substitution {k : Type} [Field k] (N : ℕ) (b : k) (hb : b ≠ 0)
    (f : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position k N) :
    Local.FunctionsMetaplectic.Construction.substitutionOperator (scalarLinearMatrix N b hb) f x = f (b⁻¹ • x) := by
  rw [Local.FunctionsMetaplectic.Construction.substitutionOperator_apply]
  congr 1
  change ((Matrix.GeneralLinearGroup.scalar (Fin N) (Units.mk0 b hb))⁻¹).val.mulVec x = b⁻¹ • x
  rw [← map_inv, Matrix.GeneralLinearGroup.coe_scalar]
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0, Matrix.scalar_apply]
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

variable {k : Type} [NormedField k] [LocallyCompactSpace k]

theorem scalarLinearMatrix_modulus (N : ℕ) (b : k) (hb : b ≠ 0) :
    Local.FunctionsMetaplectic.Construction.localModulus k (Local.FunctionsMetaplectic.Construction.determinantUnit k (scalarLinearMatrix N b hb)) = (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) ^ N := by
  have hd : Local.FunctionsMetaplectic.Construction.determinantUnit k (scalarLinearMatrix N b hb) = (Units.mk0 b hb) ^ N := by
    apply Units.ext
    change (Matrix.scalar (Fin N) b).det = b ^ N
    simp [Matrix.scalar_apply]
  rw [hd, Local.FunctionsMetaplectic.Construction.localModulus, map_pow, NNReal.coe_pow, ← DeterminantMeasure.LocalAnalysis.haarModulus_unit]
  rfl

theorem scalarLinearMatrix_factor (N : ℕ) (b : k) (hb : b ≠ 0) :
    ((Real.sqrt (Local.FunctionsMetaplectic.Construction.localModulus k (Local.FunctionsMetaplectic.Construction.determinantUnit k (scalarLinearMatrix N b hb))))⁻¹ : ℂ) =
      ((Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ))⁻¹ : ℂ) ^ N := by
  rw [scalarLinearMatrix_modulus]
  have hs : Real.sqrt ((DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) ^ N) = Real.sqrt (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) ^ N := by
    induction N with
    | zero => simp
    | succ N ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg (NNReal.coe_nonneg _) N), ih, pow_succ]
  rw [hs, Complex.ofReal_pow, inv_pow]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ScalarLeviNormalization.LocalAnalysis
