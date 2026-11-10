module

public import ArtinMatthews.MarkedSparsePhaseKernel
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
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


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

theorem markedDyadicPolynomial_continuous (L R : ℕ) (U : ℝ) (a : ℕ → ℂ) :
    Continuous (markedDyadicPolynomial L R U a) := by
  unfold markedDyadicPolynomial markedPrimePhase
  fun_prop

theorem markedDyadicPolynomial_norm_sq_continuous (L R : ℕ) (U : ℝ) (a : ℕ → ℂ) :
    Continuous (fun t => ‖markedDyadicPolynomial L R U a t‖^2) :=
  (markedDyadicPolynomial_continuous L R U a).norm.pow 2

end ArtinMatthews
