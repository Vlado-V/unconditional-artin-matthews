module

public import ArtinMatthews.MarkedMajorArcCenteredCoefficient
public import ArtinMatthews.MarkedMajorArcProductPolynomial
public import ArtinMatthews.MarkedSparsePhaseKernel
public import ArtinMatthews.MarkedMajorArcCoefficientBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Global finite bounds for the actual coefficient polynomials. These
are used only to justify Mellin/Fubini integrability, not for cancellation. -/
namespace ArtinMatthews
open Finset

theorem markedNaturalPolynomial_norm_le (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖markedNaturalPolynomial S a t‖ ≤ ∑ n ∈ S,‖a n‖ := by
  unfold markedNaturalPolynomial
  simpa only [norm_mul,markedPrimePhase_norm,mul_one] using
    norm_sum_le S (fun n => a n*markedPrimePhase n t)

theorem marked_centered_sum_bounded {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W modulation H u v : ℝ) :
    ∃ B : ℝ,∀ t : ℝ,‖markedMajorCenteredSum χ W modulation t H u v‖ ≤ B := by
  refine ⟨∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊,‖(H:ℂ)⁻¹*(markedMajorCenteredCoefficient W modulation n*χ (n:ZMod q))‖,?_⟩
  intro t
  rw [marked_centered_sum_eq_natural]
  exact markedNaturalPolynomial_norm_le _ _ _

theorem marked_dyadic_sum_bounded (l r : ℕ) (U : ℝ) (β : ℕ → ℂ) :
    ∃ B : ℝ,∀ t : ℝ,‖markedDyadicPolynomial l r U β t‖ ≤ B := by
  refine ⟨(∑ n ∈ Icc l r,‖β n‖)/|U|,?_⟩
  intro t
  unfold markedDyadicPolynomial
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg U)
  simpa only [norm_mul,markedPrimePhase_norm,mul_one] using
    norm_sum_le (Icc l r) (fun n => β n*markedPrimePhase n t)

end ArtinMatthews
