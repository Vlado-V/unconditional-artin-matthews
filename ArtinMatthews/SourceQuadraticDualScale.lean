module

public import ArtinMatthews.SourceQuadraticPoissonErrorSeparation
public import ArtinMatthews.SourceQuadraticSmallIntegrand
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

/-! Exact dual Mellin scales before any norm estimate. -/
namespace ArtinMatthews
open Complex
noncomputable section

theorem quadraticDual_sqrt_ratio_cpow {X Q N : ℝ}
    (hX : 0 < X) (hQ : 0 < Q) (hN : 0 < N) (s : ℂ) :
    (Real.sqrt (Q / (X * N)) : ℂ) ^ s =
      (Q : ℂ) ^ (s / 2) * (X : ℂ) ^ (-(s / 2)) * (N : ℂ) ^ (-(s / 2)) := by
  rw [quadraticSmall_sqrt_ratio_cpow hQ (mul_pos hX hN), Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hX.le hN.le]
  ring

theorem quadraticDual_normalized_sqrt_cpow {X Q N : ℝ}
    (hX : 0 < X) (hQ : 0 < Q) (hN : 0 < N) (s : ℂ) :
    ((X / Real.sqrt Q : ℝ) : ℂ) * (Real.sqrt (Q / (X * N)) : ℂ) ^ s =
      (X : ℂ) ^ (1 - s / 2) * (Q : ℂ) ^ ((s - 1) / 2) *
        (N : ℂ) ^ (-(s / 2)) := by
  rw [quadraticDual_sqrt_ratio_cpow hX hQ hN]
  have hXpow : (X : ℂ) ^ (1 - s / 2) = (X : ℂ) * (X : ℂ) ^ (-(s / 2)) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne'),
      Complex.cpow_one]
  have hQpow : (Q : ℂ) ^ ((s - 1) / 2) =
      (Q : ℂ) ^ (s / 2) / (Real.sqrt Q : ℂ) := by
    rw [show (s - 1) / 2 = s / 2 - 1 / 2 by ring,
      Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hQ.ne'),
      ← quadraticPoisson_sqrt_cpow hQ.le (1 : ℂ), Complex.cpow_one]
  rw [hXpow, hQpow, Complex.ofReal_div]
  ring

theorem quadraticDual_normalized_pair_cpow {X b c N R : ℝ}
    (hX : 0 < X) (hb : 0 < b) (hc : 0 < c) (hN : 0 < N) (hR : 0 < R) (s : ℂ) :
    ((X / Real.sqrt (b * c) : ℝ) : ℂ) *
        (Real.sqrt ((b * c) / (X * N)) : ℂ) ^ s =
      (X : ℂ) ^ (1 - s / 2) * (R : ℂ) ^ (s - 1) * (N : ℂ) ^ (-(s / 2)) *
        quadraticPoissonAnnularTwist R b ((s - 1) / 2) *
        quadraticPoissonAnnularTwist R c ((s - 1) / 2) := by
  rw [quadraticDual_normalized_sqrt_cpow hX (mul_pos hb hc) hN]
  have hbR := div_pos hb hR
  have hcR := div_pos hc hR
  have he : b * c = R * R * (b / R) * (c / R) := by field_simp
  have hpower : ((b * c : ℝ) : ℂ) ^ ((s - 1) / 2) =
      (R : ℂ) ^ (s - 1) * quadraticPoissonAnnularTwist R b ((s - 1) / 2) *
        quadraticPoissonAnnularTwist R c ((s - 1) / 2) := by
    rw [he, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (mul_pos (mul_pos hR hR) hbR).le hcR.le,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (mul_pos hR hR).le hbR.le,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hR.le hR.le,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hR.ne')]
    rw [show (s - 1) / 2 + (s - 1) / 2 = s - 1 by ring]
    rfl
  rw [hpower]
  ring

end
end ArtinMatthews
