module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
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


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set
open scoped BigOperators
noncomputable section

/-- The regular spectral window in ABL Section 6, with the width left explicit. -/
def spectralABLRegularWindow (T Δ : ℝ) (z : ℂ) : ℂ :=
  (z ^ 2 + 1 / 4) / (T : ℂ) ^ 2 *
    (Complex.exp (-(((z - (T : ℂ)) / (Δ : ℂ)) ^ 2)) +
      Complex.exp (-(((z + (T : ℂ)) / (Δ : ℂ)) ^ 2)))

def spectralABLRegularWindowReal (T Δ t : ℝ) : ℝ :=
  (t ^ 2 + 1 / 4) / T ^ 2 *
    (Real.exp (-(((t - T) / Δ) ^ 2)) + Real.exp (-(((t + T) / Δ) ^ 2)))

theorem spectralABLRegularWindow_real (T Δ t : ℝ) :
    spectralABLRegularWindow T Δ (t : ℂ) = (spectralABLRegularWindowReal T Δ t : ℂ) := by
  unfold spectralABLRegularWindow spectralABLRegularWindowReal
  push_cast
  rfl

theorem spectralABLRegularWindow_even (T Δ : ℝ) (z : ℂ) :
    spectralABLRegularWindow T Δ (-z) = spectralABLRegularWindow T Δ z := by
  unfold spectralABLRegularWindow
  have hminus : (-z - (T : ℂ)) / (Δ : ℂ) = -((z + (T : ℂ)) / (Δ : ℂ)) := by ring
  have hplus : (-z + (T : ℂ)) / (Δ : ℂ) = -((z - (T : ℂ)) / (Δ : ℂ)) := by ring
  rw [hminus, hplus]
  simp only [neg_sq]
  rw [add_comm (Complex.exp _) (Complex.exp _)]

theorem spectralABLRegularWindow_differentiable (T Δ : ℝ) :
    Differentiable ℂ (spectralABLRegularWindow T Δ) := by
  unfold spectralABLRegularWindow
  fun_prop

theorem spectralABLRegularWindowReal_nonneg (T Δ t : ℝ) :
    0 ≤ spectralABLRegularWindowReal T Δ t := by
  unfold spectralABLRegularWindowReal
  positivity

/-- The exceptional window, including every pole-cancelling factor. -/
def spectralABLExceptionalWindow (a : ℝ) (A : ℕ) (z : ℂ) : ℂ :=
  (2 * Complex.cos (2 * z * (Real.log a : ℂ))) ^ 2 /
      (z ^ 2 + (2 * (A : ℂ)) ^ 2) ^ (2 * A) *
    ∏ k ∈ Finset.range (A + 1), (z ^ 2 + (((2 * k + 1 : ℕ) : ℂ) / 2) ^ 2)

def spectralABLExceptionalWindowReal (a : ℝ) (A : ℕ) (t : ℝ) : ℝ :=
  (2 * Real.cos (2 * t * Real.log a)) ^ 2 /
      (t ^ 2 + (2 * (A : ℝ)) ^ 2) ^ (2 * A) *
    ∏ k ∈ Finset.range (A + 1), (t ^ 2 + (((2 * k + 1 : ℕ) : ℝ) / 2) ^ 2)

theorem spectralABLExceptionalWindow_real (a : ℝ) (A : ℕ) (t : ℝ) :
    spectralABLExceptionalWindow a A (t : ℂ) = (spectralABLExceptionalWindowReal a A t : ℂ) := by
  unfold spectralABLExceptionalWindow spectralABLExceptionalWindowReal
  push_cast
  rfl

theorem spectralABLExceptionalWindow_even (a : ℝ) (A : ℕ) (z : ℂ) :
    spectralABLExceptionalWindow a A (-z) = spectralABLExceptionalWindow a A z := by
  unfold spectralABLExceptionalWindow
  rw [show 2 * -z * (Real.log a : ℂ) = -(2 * z * (Real.log a : ℂ)) by ring,
    Complex.cos_neg]
  simp only [neg_sq]

theorem spectralABLExceptionalWindowReal_nonneg (a : ℝ) (A : ℕ) (t : ℝ) :
    0 ≤ spectralABLExceptionalWindowReal a A t := by
  unfold spectralABLExceptionalWindowReal
  apply mul_nonneg (div_nonneg (sq_nonneg _) (pow_nonneg (by positivity) _))
  exact Finset.prod_nonneg (fun _ _ => by positivity)

end
end ArtinMatthews
