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
public import OAI.RepresentationTheory.Weil.Local.FourierTools
public import OAI.RepresentationTheory.Weil.Local.QuadraticIntertwiner


set_option backward.privateInPublic true
@[expose] public section

/-! # General Quadratic Algebra -/

namespace OAI.RepresentationTheory.Weil.Local.GeneralQuadraticAlgebra.Construction

noncomputable section

/-! Completing the square for a nonsingular symmetric matrix. -/

open _root_.Matrix

theorem general_quadratic_complete_square
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (M : FunctionsMetaplectic.Construction.GeneralLinear k n) (hM : M.val.IsSymm) (x y : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.quadratic M.val (y + M⁻¹.val *ᵥ x) - FunctionsMetaplectic.Construction.dot x (y + M⁻¹.val *ᵥ x) =
      FunctionsMetaplectic.Construction.quadratic M.val y - FunctionsMetaplectic.Construction.quadratic M⁻¹.val x := by
  have hcancel : M.val *ᵥ (M⁻¹.val *ᵥ x) = x := by
    rw [mulVec_mulVec]
    have h : M.val * M⁻¹.val = 1 := congrArg Units.val (mul_inv_cancel M)
    rw [h, one_mulVec]
  have hcross : FunctionsMetaplectic.Construction.dot (M⁻¹.val *ᵥ x) (M.val *ᵥ y) = FunctionsMetaplectic.Construction.dot y x := by
    have h := Matrix.dotProduct_transpose_mulVec M.val (M⁻¹.val *ᵥ x) y
    change (M⁻¹.val *ᵥ x) ⬝ᵥ M.val *ᵥ y = y ⬝ᵥ x
    simpa only [hM.eq, hcancel] using h
  rw [QuadraticIntertwiner.Construction.quadratic_eq_dot, QuadraticIntertwiner.Construction.quadratic_eq_dot, QuadraticIntertwiner.Construction.quadratic_eq_dot]
  change ((y + M⁻¹.val *ᵥ x) ⬝ᵥ M.val *ᵥ (y + M⁻¹.val *ᵥ x)) / 2 -
    x ⬝ᵥ (y + M⁻¹.val *ᵥ x) = (y ⬝ᵥ M.val *ᵥ y) / 2 -
      (x ⬝ᵥ M⁻¹.val *ᵥ x) / 2
  simp only [mulVec_add, hcancel, add_dotProduct, dotProduct_add]
  change (FunctionsMetaplectic.Construction.dot y (M.val *ᵥ y) + FunctionsMetaplectic.Construction.dot (M⁻¹.val *ᵥ x) (M.val *ᵥ y) +
    (FunctionsMetaplectic.Construction.dot y x + FunctionsMetaplectic.Construction.dot (M⁻¹.val *ᵥ x) x)) / 2 -
      (FunctionsMetaplectic.Construction.dot x y + FunctionsMetaplectic.Construction.dot x (M⁻¹.val *ᵥ x)) = _
  rw [hcross, FourierTools.Construction.dot_comm y x, FourierTools.Construction.dot_comm (M⁻¹.val *ᵥ x) x]
  unfold FunctionsMetaplectic.Construction.dot dotProduct
  ring

end

end OAI.RepresentationTheory.Weil.Local.GeneralQuadraticAlgebra.Construction
