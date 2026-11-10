module

public import ArtinMatthews.SpectralJRegularizedEnergyTest
public import ArtinMatthews.SpectralABLMultiplierReality
public import ArtinMatthews.SpectralJForwardReality
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

open Complex Set
open scoped ContDiff ComplexConjugate
noncomputable section

theorem spectralJRegularizerPrimitive_conj (L : ℝ) (w : ℂ) :
    conj (spectralJRegularizerPrimitive L w) = spectralJRegularizerPrimitive L (conj w) := by
  rw [spectralJRegularizerPrimitive_integral, spectralJRegularizerPrimitive_integral,
    ← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro s _
  change conj (Complex.exp (-(s : ℂ) * w)) = Complex.exp (-(s : ℂ) * conj w)
  rw [← Complex.exp_conj]
  simp only [map_mul, map_neg, Complex.conj_ofReal]

theorem spectralJRegularizedWeight_conj (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (hReal : ∀ x : ℝ, conj (f x) = f x) (L : ℝ) (z : ℂ) :
    conj (spectralJRegularizedWeight f L z) = spectralJRegularizedWeight f L (conj z) := by
  have hC := spectralABLCoshCancellation_conj z
  change conj (spectralABLCoshCancellation z) = spectralABLCoshCancellation (conj z) at hC
  simp only [spectralJRegularizedWeight, map_mul, Complex.conj_ofReal,
    spectralJForwardTransform_conj f hf hc hp hReal z, hC,
    spectralJRegularizerPrimitive_conj, map_add, map_pow, map_div₀, map_ofNat, map_one]

theorem spectralJRegularizedEnergyTest_real (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (hReal : ∀ x : ℝ, conj (f x) = f x) (L : ℝ) (hL : 0 ≤ L)
    (l : Ici (0 : ℝ)) :
    star (spectralJRegularizedEnergyTest f hf hc hp L hL l) =
      spectralJRegularizedEnergyTest f hf hc hp L hL l := by
  rw [spectralJRegularizedEnergyTest_apply]
  change conj (spectralJRegularizedWeight f L (spectralSourceParameter l)) = _
  rw [spectralJRegularizedWeight_conj f hf.continuous hc hp hReal L]
  by_cases hl : 1 / 4 ≤ (l : ℝ)
  · rw [spectralSourceParameter_principal l hl, Complex.conj_ofReal]
  · have hparam : spectralSourceParameter l =
        (Real.sqrt (1 / 4 - (l : ℝ)) : ℂ) * I := by
      rw [spectralSourceParameter, Real.sqrt_eq_zero_of_nonpos (by linarith)]
      simp only [Complex.ofReal_zero, zero_add]
    rw [hparam, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
      spectralJRegularizedWeight_even]

end
end ArtinMatthews
