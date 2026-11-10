module

public import ArtinMatthews.SourceKPNormalizedBorel
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import ArtinMatthews.SourceKPCommRingDiagonal
public import ArtinMatthews.SourceKubotaBottomRows
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.CStarAlgebra.Classes
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


set_option backward.privateInPublic true
@[expose] public section

/-! The scalar spherical section on the actual complex projective
linear group. Its height uses the full bottom row and determinant. -/
namespace ArtinMatthews.SourceArchJacquet

open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

def sourceArchBottomNorm (g : GL (Fin 2) ℂ) : ℝ :=
  ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2

theorem sourceArchBottomNorm_pos (g : GL (Fin 2) ℂ) : 0 < sourceArchBottomNorm g := by
  by_cases h : g 1 0 = 0
  · have h' := sourceGL2_bottom_right_ne_zero g h
    unfold sourceArchBottomNorm
    rw [h, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
    exact sq_pos_of_pos (norm_pos_iff.mpr h')
  · exact lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr h))
      (le_add_of_nonneg_right (sq_nonneg _))

def sourceArchHeight (g : GL (Fin 2) ℂ) : ℝ :=
  ‖(GeneralLinearGroup.det g : ℂ)‖ / sourceArchBottomNorm g

theorem sourceArchHeight_pos (g : GL (Fin 2) ℂ) : 0 < sourceArchHeight g :=
  div_pos (norm_pos_iff.mpr (Units.ne_zero (GeneralLinearGroup.det g))) (sourceArchBottomNorm_pos g)

theorem sourceArchBottomNorm_scalar (g : GL (Fin 2) ℂ) (u : ℂˣ) :
    sourceArchBottomNorm (g * GeneralLinearGroup.scalar (Fin 2) u) =
      sourceArchBottomNorm g * ‖(u : ℂ)‖ ^ 2 := by
  unfold sourceArchBottomNorm
  rw [sourceKPMatrix_right_scalar_entry, sourceKPMatrix_right_scalar_entry, norm_mul, norm_mul,
    mul_pow, mul_pow]
  ring

theorem sourceArchHeight_scalar (g : GL (Fin 2) ℂ) (u : ℂˣ) :
    sourceArchHeight (g * GeneralLinearGroup.scalar (Fin 2) u) = sourceArchHeight g := by
  unfold sourceArchHeight
  rw [sourceArchBottomNorm_scalar, map_mul, GeneralLinearGroup.det_scalar]
  simp only [Fintype.card_fin, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow]
  exact mul_div_mul_right _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr u.ne_zero))

def sourceArchSphericalGL (s : ℂ) (g : GL (Fin 2) ℂ) : ℂ :=
  (sourceArchHeight g : ℂ) ^ (2 * s + 1)

theorem sourceArchSphericalGL_scalar (s : ℂ) (g : GL (Fin 2) ℂ) (u : ℂˣ) :
    sourceArchSphericalGL s (g * GeneralLinearGroup.scalar (Fin 2) u) = sourceArchSphericalGL s g := by
  rw [sourceArchSphericalGL, sourceArchHeight_scalar, sourceArchSphericalGL]

def sourceArchSphericalSection (s : ℂ) (g : PGL(2, ℂ)) : ℂ :=
  Quotient.liftOn g (sourceArchSphericalGL s) (by
    intro a b hab
    have he : ProjGenLinGroup.mk a = ProjGenLinGroup.mk b := Quotient.sound hab
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
    rw [← hu, sourceArchSphericalGL_scalar])

theorem sourceArchSphericalSection_mk (s : ℂ) (g : GL (Fin 2) ℂ) :
    sourceArchSphericalSection s (ProjGenLinGroup.mk g) = sourceArchSphericalGL s g := rfl

theorem sourceArchHeight_borel (b g : GL (Fin 2) ℂ) (hb : b ∈ sourceGL2NormalizedBorel ℂ) :
    sourceArchHeight (b * g) = ‖(GeneralLinearGroup.det b : ℂ)‖ * sourceArchHeight g := by
  have h := sourceGL2NormalizedBorel_bottom ℂ b hb
  have hden : sourceArchBottomNorm (b * g) = sourceArchBottomNorm g := by
    unfold sourceArchBottomNorm
    rw [sourceGL2_bottom_left_mul, sourceGL2_bottom_right_mul, h.1, h.2]
    simp
  unfold sourceArchHeight
  rw [hden, map_mul, Units.val_mul, norm_mul, mul_div_assoc]

theorem sourceArchSphericalSection_borel (s : ℂ) (b g : GL (Fin 2) ℂ)
    (hb : b ∈ sourceGL2NormalizedBorel ℂ) :
    sourceArchSphericalSection s (ProjGenLinGroup.mk b * ProjGenLinGroup.mk g) =
      (‖(GeneralLinearGroup.det b : ℂ)‖ : ℂ) ^ (2 * s + 1) *
        sourceArchSphericalSection s (ProjGenLinGroup.mk g) := by
  rw [← map_mul, sourceArchSphericalSection_mk, sourceArchSphericalGL, sourceArchHeight_borel b g hb,
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (sourceArchHeight_pos g).le,
    sourceArchSphericalSection_mk, sourceArchSphericalGL]

theorem sourceArchSphericalSection_one (s : ℂ) : sourceArchSphericalSection s 1 = 1 := by
  change sourceArchSphericalGL s 1 = 1
  simp [sourceArchSphericalGL, sourceArchHeight, sourceArchBottomNorm]

theorem sourceArchSphericalSection_bigCell (s : ℂ) (x : ℂ) (y : ℂˣ) :
    sourceArchSphericalSection s (sourcePGL2Weyl * sourcePGL2Upper x * sourcePGL2Diagonal y) =
      ((‖(y : ℂ)‖ / (‖(y : ℂ)‖ ^ 2 + ‖x‖ ^ 2) : ℝ) : ℂ) ^ (2 * s + 1) := by
  rw [← map_mul, ← map_mul, sourceArchSphericalSection_mk, sourceArchSphericalGL, sourceArchHeight]
  have hdet : ‖(GeneralLinearGroup.det ((sourceGL2Weyl : GL (Fin 2) ℂ) *
      sourceGL2Upper x * sourceGL2Diagonal y) : ℂ)‖ = ‖(y : ℂ)‖ := by
    simp [map_mul, sourceGL2Weyl, sourceGL2Upper, sourceGL2Diagonal, GeneralLinearGroup.val_det_apply,
      Matrix.det_fin_two]
  have hden : sourceArchBottomNorm ((sourceGL2Weyl : GL (Fin 2) ℂ) * sourceGL2Upper x * sourceGL2Diagonal y) =
      ‖(y : ℂ)‖ ^ 2 + ‖x‖ ^ 2 := by
    simp [sourceArchBottomNorm, sourceGL2_right_diagonal_bottom_left, sourceGL2_right_diagonal_bottom_right,
      sourceGL2_right_upper_bottom_left, sourceGL2_right_upper_bottom_right, sourceGL2Weyl]
  rw [hdet, hden]

end
end ArtinMatthews.SourceArchJacquet
