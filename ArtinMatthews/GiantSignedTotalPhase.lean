module

public import ArtinMatthews.IdealLabelOperator
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
noncomputable section

/-- The spectral derivative multiplier factors at the literal natural product. -/
theorem giantSignedTotalD_cpow (d D : ℕ) (ζ : ℝ) :
    ((d * D : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I) =
      (d : ℂ) ^ ((ζ : ℂ) * Complex.I) * (D : ℂ) ^ ((ζ : ℂ) * Complex.I) := by
  simpa only [Nat.cast_mul] using
    Complex.natCast_mul_natCast_cpow d D ((ζ : ℂ) * Complex.I)

/-- The original additive frequency scales by the fixed small product. -/
theorem idealAdditivePhase_totalD (θ : ℝ) (d D : ℕ) :
    idealAdditivePhase θ (d * D) = idealAdditivePhase (θ * (d : ℝ)) D := by
  unfold idealAdditivePhase
  congr 1
  push_cast
  ring

/-- Exact separation of both original phase factors at the total product. -/
theorem giantSignedTotalD_multiplier (θ ζ : ℝ) (d D : ℕ) :
    ((d * D : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I) * idealAdditivePhase θ (d * D) =
      (d : ℂ) ^ ((ζ : ℂ) * Complex.I) *
        ((D : ℂ) ^ ((ζ : ℂ) * Complex.I) * idealAdditivePhase (θ * (d : ℝ)) D) := by
  rw [giantSignedTotalD_cpow, idealAdditivePhase_totalD]
  ring

/-- The fixed positive small product contributes a unit-modulus multiplier. -/
theorem giantSignedSmallD_cpow_norm (d : ℕ) (hd : 0 < d) (ζ : ℝ) :
    ‖(d : ℂ) ^ ((ζ : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hd]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, mul_zero, zero_mul, sub_self, Real.rpow_zero]

end
end ArtinMatthews
