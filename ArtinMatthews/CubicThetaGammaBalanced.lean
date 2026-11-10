module

public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Data.Rat.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Int.Star
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Basify


set_option backward.privateInPublic true
@[expose] public section

/-! Balanced integer reductions used in the elementary generation of `Γ₁(3)`. -/

namespace ArtinMatthews

/-- Adding a suitable integer multiple of a nonzero integer leaves an absolute
remainder at most half the absolute modulus. -/
theorem exists_balanced_add_mul (a c : ℤ) (hc : c ≠ 0) :
    ∃ n : ℤ, 2 * |a + n * c| ≤ |c| := by
  let r : ℤ := round ((a : ℚ) / (c : ℚ))
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  have h := mul_le_mul_of_nonneg_right
    (abs_sub_round ((a : ℚ) / (c : ℚ))) (abs_nonneg (c : ℚ))
  have heq : ((a : ℚ) / (c : ℚ) - (r : ℚ)) * (c : ℚ) =
      (a : ℚ) - (r : ℚ) * (c : ℚ) := by
    dsimp [r]
    field_simp
  change |(a : ℚ) / (c : ℚ) - (r : ℚ)| * |(c : ℚ)| ≤ _ at h
  rw [← abs_mul, heq] at h
  refine ⟨-r, ?_⟩
  have hcast : (2 : ℚ) * |((a + (-r) * c : ℤ) : ℚ)| ≤ |(c : ℚ)| := by
    push_cast
    have he : (a : ℚ) + -(r : ℚ) * (c : ℚ) =
        (a : ℚ) - (r : ℚ) * (c : ℚ) := by ring
    rw [he]
    linarith
  exact_mod_cast hcast

/-- The same reduction along multiples of `3a`. -/
theorem exists_three_balanced_add_mul (c a : ℤ) (ha : a ≠ 0) :
    ∃ n : ℤ, 2 * |c + 3 * n * a| ≤ 3 * |a| := by
  obtain ⟨n, hn⟩ := exists_balanced_add_mul c (3 * a) (mul_ne_zero (by norm_num) ha)
  refine ⟨n, ?_⟩
  calc
    2 * |c + 3 * n * a| = 2 * |c + n * (3 * a)| := by congr 2; ring
    _ ≤ |3 * a| := hn
    _ = 3 * |a| := by simp [abs_mul]

end ArtinMatthews
