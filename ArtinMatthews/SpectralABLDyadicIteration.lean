module

public import ArtinMatthews.SpectralKLCompactIteration
public import ArtinMatthews.SpectralABLDyadicOperator
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
public import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set
open scoped ContDiff
noncomputable section

theorem spectralKLIteratedOperator_tsupport (f : ℝ → ℂ) (k : ℕ) :
    tsupport (spectralKLIteratedOperator f k) ⊆ tsupport f := by
  induction k with
  | zero => exact Subset.rfl
  | succ k ih => exact (spectralKLShiftedOperator_tsupport _).trans ih

private theorem spectralKLIteratedOperator_smooth (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (spectralKLIteratedOperator f k) := by
  induction k with
  | zero => exact hf
  | succ k ih => exact spectralKLShiftedOperator_smooth _ ih

theorem spectralKLIteratedOperator_dyadic_deriv (k J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Z M : ℝ) (f : ℝ → ℂ),
      0 < X → 1 ≤ Z → X ≤ Z → 0 ≤ M → ContDiff ℝ ∞ f →
      (∀ j ≤ J+2*k, ∀ x ∈ Icc X (2*X), (X/Z)^j*‖iteratedDeriv j f x‖ ≤ M) →
      ∀ j ≤ J, ∀ x ∈ Icc X (2*X),
        (X/Z)^j*‖iteratedDeriv j (spectralKLIteratedOperator f k) x‖ ≤ C*Z^(2*k)*M := by
  induction k generalizing J with
  | zero =>
    refine ⟨1,zero_lt_one,?_⟩
    intro X Z M f hX hZ hXZ hM hf hF j hj x hx
    simpa only [spectralKLIteratedOperator,Nat.mul_zero,pow_zero,one_mul] using
      hF j (by omega) x hx
  | succ k ih =>
    obtain ⟨D,hD,hiter⟩ := ih (J+2)
    obtain ⟨E,hE,hshift⟩ := spectralKLShiftedOperator_dyadic_deriv J
    refine ⟨E*D,mul_pos hE hD,?_⟩
    intro X Z M f hX hZ hXZ hM hf hF j hj x hx
    let g := spectralKLIteratedOperator f k
    have hg : ContDiff ℝ ∞ g := spectralKLIteratedOperator_smooth f hf k
    have hZ' : 0 ≤ Z := zero_le_one.trans hZ
    have hbound := hshift X Z (D*Z^(2*k)*M) g hX hZ hXZ (by positivity) hg
      (hiter X Z M f hX hZ hXZ hM hf (fun j hj x hx => hF j (by omega) x hx)) j hj x hx
    change (X/Z)^j*‖iteratedDeriv j (spectralKLShiftedOperator g) x‖ ≤ _
    refine hbound.trans_eq ?_
    rw [show 2*(k+1) = 2*k+2 by omega,pow_add]
    ring

end
end ArtinMatthews
