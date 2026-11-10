module

public import ArtinMatthews.SourceArchDiagonalDerivative
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ArtinMatthews.SourceArchLogCompact
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

theorem sourceArchPositiveDiagonal_zero : sourceArchPositiveDiagonal 0 = 1 := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceArchPositiveDiagonal, sourceKPDiagonalHom]

theorem sourceArchDiagonalLog_zero (g : GL (Fin 2) ℂ) :
    sourceArchDiagonalLog g 0 = Real.log (sourceArchHeight g) := by
  rw [sourceArchDiagonalLog_eq, sourceArchPositiveDiagonal_zero, mul_one]

theorem sourceArchDiagonalLog_compact_bound (g : GL (Fin 2) ℂ) {t R : ℝ}
    (ht : |t| ≤ R) : |sourceArchDiagonalLog g t - sourceArchDiagonalLog g 0| ≤ R := by
  have h := sourceArch_log_lipschitz (sourceArchDiagonalLog_hasDerivAt g)
    (fun x => (sourceArchDiagonalLog_bounds g x).1) t 0
  exact h.trans (by simpa only [sub_zero, one_mul] using ht)

theorem sourceArchDiagonalSection_compact_bound (s : ℂ) (g : GL (Fin 2) ℂ)
    {R t B : ℝ} (ht : |t| ≤ R) (hs : |(2*s+1).re| ≤ B) :
    ‖sourceArchDiagonalSection s g t‖ ≤
      Real.exp (B*R) * (sourceArchHeight g)^((2*s+1).re) := by
  have h := sourceArch_log_profile_bound (sourceArchDiagonalLog_compact_bound g ht) hs
  rw [sourceArchDiagonalSection_eq_exp, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simpa only [sourceArchDiagonalLog_zero, Real.rpow_def_of_pos (sourceArchHeight_pos g)] using h

theorem sourceArchDiagonalSection_deriv_compact_bound (s : ℂ) (g : GL (Fin 2) ℂ)
    {R t B : ℝ} (ht : |t| ≤ R) (hs : |(2*s+1).re| ≤ B) :
    ‖deriv (sourceArchDiagonalSection s g) t‖ ≤
      Real.exp (B*R) * ‖2*s+1‖ * (sourceArchHeight g)^((2*s+1).re) := by
  calc
    _ ≤ ‖2*s+1‖*‖sourceArchDiagonalSection s g t‖ := sourceArchDiagonalSection_deriv_bound s g t
    _ ≤ ‖2*s+1‖*(Real.exp (B*R) * (sourceArchHeight g)^((2*s+1).re)) :=
      mul_le_mul_of_nonneg_left (sourceArchDiagonalSection_compact_bound s g ht hs) (norm_nonneg _)
    _ = _ := by ring

theorem sourceArchDiagonalSection_deriv_two_compact_bound (s : ℂ) (g : GL (Fin 2) ℂ)
    {R t B : ℝ} (ht : |t| ≤ R) (hs : |(2*s+1).re| ≤ B) :
    ‖deriv (deriv (sourceArchDiagonalSection s g)) t‖ ≤
      Real.exp (B*R) * (‖2*s+1‖^2+‖2*s+1‖) * (sourceArchHeight g)^((2*s+1).re) := by
  calc
    _ ≤ (‖2*s+1‖^2+‖2*s+1‖)*‖sourceArchDiagonalSection s g t‖ :=
      sourceArchDiagonalSection_deriv_two_bound s g t
    _ ≤ (‖2*s+1‖^2+‖2*s+1‖)*(Real.exp (B*R) * (sourceArchHeight g)^((2*s+1).re)) :=
      mul_le_mul_of_nonneg_left (sourceArchDiagonalSection_compact_bound s g ht hs) (by positivity)
    _ = _ := by ring

end
end ArtinMatthews.SourceArchJacquet
