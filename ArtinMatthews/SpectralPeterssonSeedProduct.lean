module

public import ArtinMatthews.SpectralHolomorphicCuspSeed
public import ArtinMatthews.SpectralCuspDiagonalFourierIntegral
public import ArtinMatthews.SpectralCuspTranslationAdmissibility
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Exact horizontal Fourier factors in the physical norm of a
holomorphic seed packet. -/
noncomputable section
open Set MeasureTheory UpperHalfPlane
open scoped ComplexConjugate

namespace ArtinMatthews

theorem spectralHolomorphicCuspSeed_pair (m n : ℕ+) (z : UpperHalfPlane) :
    conj (spectralHolomorphicCuspSeed (m : ℕ) z)*spectralHolomorphicCuspSeed (n : ℕ) z =
      atkinPhase (((n : ℝ)-(m : ℝ))*z.re)*
        (Real.exp (-(2*Real.pi*((m : ℝ)+(n : ℝ))*z.im)) : ℂ) := by
  unfold spectralHolomorphicCuspSeed atkinPhase
  rw [← Complex.exp_conj,← Complex.exp_add,Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  apply Complex.ext <;>
    simp [Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im] <;> ring

theorem spectralPeterssonPhase_integral (d : ℤ) :
    (∫ x in Ioc (0 : ℝ) 1, atkinPhase ((d : ℝ)*x)) = if d = 0 then 1 else 0 := by
  have he : (fun x : ℝ => atkinPhase ((d : ℝ)*x)) = cuspFourierPhase 1 (-d) := by
    funext x
    rw [cuspFourierPhase_as_atkinPhase]
    congr 1
    push_cast
    ring
  rw [he,← intervalIntegral.integral_of_le zero_le_one]
  simpa only [neg_eq_zero,Complex.ofReal_one] using cuspFourierPhase_integral_full_period 1 zero_lt_one (-d)

end ArtinMatthews
