module

public import ArtinMatthews.MarkedMinorArcGram
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The source integer bilinear bound with both coefficient energies and
both interval origins retained. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

private abbrev RP := OAI.Problem337.RealPhase.phase

theorem idealIntegerPhase_eq (x : ℝ) : RP x = (Real.fourierChar x : ℂ) := by
  change Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) = _
  rw [Real.fourierChar_apply]
  congr 1
  exact mul_comm _ _

theorem idealIntegerBilinear_sq_le (L T : ℤ) (M N : ℕ) (α : ℝ) (u : ℤ)
    (q : ℕ) (hq : 0 < q) (hcop : IsCoprime u (q : ℤ))
    (happrox : |α - (u : ℝ)/q| ≤ 1/(q : ℝ)^2) (a b : ℤ → ℂ) :
    ‖∑ h ∈ Ico L (L+(M : ℤ)), a h *
      ∑ n ∈ Ico T (T+(N : ℤ)), b n * (Real.fourierChar (α*(h : ℝ)*n) : ℂ)‖^2 ≤
      markedMinorGramBudget M N q *
        (∑ h ∈ Ico L (L+(M : ℤ)), ‖a h‖^2) *
        (∑ n ∈ Ico T (T+(N : ℤ)), ‖b n‖^2) := by
  simp_rw [← idealIntegerPhase_eq]
  have he := marked_minor_bilinear_energy_le L T M N α u q hq hcop happrox b
  calc
    _ ≤ (∑ h ∈ Ico L (L+(M : ℤ)), ‖a h‖ *
        ‖∑ n ∈ Ico T (T+(N : ℤ)), b n * RP (α*(h : ℝ)*n)‖)^2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [norm_mul] using norm_sum_le (Ico L (L+(M : ℤ)))
        (fun h => a h * ∑ n ∈ Ico T (T+(N : ℤ)), b n * RP (α*(h : ℝ)*n))
    _ ≤ (∑ h ∈ Ico L (L+(M : ℤ)), ‖a h‖^2) *
        ∑ h ∈ Ico L (L+(M : ℤ)),
          ‖∑ n ∈ Ico T (T+(N : ℤ)), b n * RP (α*(h : ℝ)*n)‖^2 :=
      sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (∑ h ∈ Ico L (L+(M : ℤ)), ‖a h‖^2) *
        (markedMinorGramBudget M N q * ∑ n ∈ Ico T (T+(N : ℤ)), ‖b n‖^2) :=
      mul_le_mul_of_nonneg_left he (sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by ring

end
end ArtinMatthews
