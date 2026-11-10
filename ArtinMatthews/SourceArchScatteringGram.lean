module

public import ArtinMatthews.SourceArchSphericalSection
public import ArtinMatthews.SourceKubotaBottomRows
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The full bottom-row Gram calculation for the translated spherical
kernel. It retains the actual entries of an arbitrary invertible matrix. -/
namespace ArtinMatthews.SourceArchJacquet

open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

theorem sourceArchGram_identity (a b c d x : ℂ) :
    (‖c‖ ^ 2 + ‖d‖ ^ 2) * (‖a + x * c‖ ^ 2 + ‖b + x * d‖ ^ 2) =
      ‖(((‖c‖ ^ 2 + ‖d‖ ^ 2 : ℝ) : ℂ) * x + (a * star c + b * star d))‖ ^ 2 +
        ‖a * d - b * c‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

def sourceArchGramShift (g : GL (Fin 2) ℂ) : ℂ :=
  (g 0 0 * star (g 1 0) + g 0 1 * star (g 1 1)) / (sourceArchBottomNorm g : ℂ)

theorem sourceArchBottomNorm_translated (g : GL (Fin 2) ℂ) (x : ℂ) :
    sourceArchBottomNorm (sourceGL2Weyl * sourceGL2Upper x * g) =
      ‖g 0 0 + x * g 1 0‖ ^ 2 + ‖g 0 1 + x * g 1 1‖ ^ 2 := by
  simp [sourceArchBottomNorm, sourceGL2Weyl, sourceGL2Upper, Matrix.mul_apply, Fin.sum_univ_two]

theorem sourceArchBottomNorm_translated_gram (g : GL (Fin 2) ℂ) (x : ℂ) :
    sourceArchBottomNorm g * sourceArchBottomNorm (sourceGL2Weyl * sourceGL2Upper x * g) =
      (sourceArchBottomNorm g) ^ 2 * ‖x + sourceArchGramShift g‖ ^ 2 +
        ‖(GeneralLinearGroup.det g : ℂ)‖ ^ 2 := by
  have h := sourceArchGram_identity (g 0 0) (g 0 1) (g 1 0) (g 1 1) x
  rw [← sourceArchBottomNorm_translated, ← sourceArchBottomNorm,
    ← sourceGL2_det_val] at h
  have hR : (sourceArchBottomNorm g : ℂ) ≠ 0 := by
    exact_mod_cast (sourceArchBottomNorm_pos g).ne'
  have he : (sourceArchBottomNorm g : ℂ) * x + (g 0 0 * star (g 1 0) + g 0 1 * star (g 1 1)) =
      (sourceArchBottomNorm g : ℂ) * (x + sourceArchGramShift g) := by
    unfold sourceArchGramShift
    field_simp
  rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sourceArchBottomNorm_pos g).le,
    mul_pow] at h
  exact h

theorem sourceArchBottomNorm_completed (g : GL (Fin 2) ℂ) (x : ℂ) :
    sourceArchBottomNorm (sourceGL2Weyl * sourceGL2Upper x * g) =
      sourceArchBottomNorm g * (‖x + sourceArchGramShift g‖ ^ 2 + (sourceArchHeight g) ^ 2) := by
  have h := sourceArchBottomNorm_translated_gram g x
  have hR := (sourceArchBottomNorm_pos g).ne'
  unfold sourceArchHeight
  field_simp
  nlinarith

theorem sourceArchHeight_translated (g : GL (Fin 2) ℂ) (x : ℂ) :
    sourceArchHeight (sourceGL2Weyl * sourceGL2Upper x * g) =
      sourceArchHeight g / (‖x + sourceArchGramShift g‖ ^ 2 + (sourceArchHeight g) ^ 2) := by
  have hdet : ‖(GeneralLinearGroup.det (sourceGL2Weyl * sourceGL2Upper x * g) : ℂ)‖ =
      ‖(GeneralLinearGroup.det g : ℂ)‖ := by
    simp [map_mul, sourceGL2Weyl, sourceGL2Upper, GeneralLinearGroup.val_det_apply,
      Matrix.det_fin_two]
    exact norm_sub_rev _ _
  rw [sourceArchHeight, hdet, sourceArchBottomNorm_completed, sourceArchHeight, div_div]

end
end ArtinMatthews.SourceArchJacquet
