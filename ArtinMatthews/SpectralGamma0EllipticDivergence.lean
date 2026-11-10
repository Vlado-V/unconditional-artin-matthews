module

public import ArtinMatthews.SpectralGamma0EllipticTests
public import OAI.Analysis.PDE.Variational.H1Divergence
public import OAI.Analysis.PDE.Weak.Elliptic.TestSupport
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import OAI.Analysis.PDE.Weak.Elliptic.SmoothGradient


set_option backward.privateInPublic true
@[expose] public section

/-! The native strong H¹ graph converts the second-order distributional
Laplacian equation into the first-order divergence formulation required by
the genuine L²-forcing interior regularity theorem. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational

namespace ArtinMatthews

theorem spectralEllipticPositiveLaplacian_eq_divergence
    (χ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) :
    spectralEllipticPositiveLaplacian χ x = -cellDivergence (cellGradient χ) x := rfl

theorem spectralElliptic_weakDivergence_of_second_tests
    (p : H1Pair 1) (hp : p ∈ H1Zero (univ : Set (Fin 2 → ℝ)))
    (f : Lp ℝ 2 (volume : Measure (Fin 2 → ℝ))) {Ω : Set (Fin 2 → ℝ)}
    (hsecond : ∀ (χ : (Fin 2 → ℝ) → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Ω →
      (∫ x, p.1 x * spectralEllipticPositiveLaplacian χ x) = ∫ x, f x * χ x) :
    WeakDivergenceEquation Ω p.2 f := by
  intro χ hχ hc hs
  have hG : ContDiff ℝ 1 (cellGradient χ) := (contDiff_cellGradient hχ).of_le (by simp)
  have he := OAI.Analysis.PDE.Variational.H1Zero.integral_divergence hp
    (cellGradient χ) hG (hasCompactSupport_cellGradient hc)
  rw [he]
  simpa only [spectralEllipticPositiveLaplacian_eq_divergence,mul_neg,integral_neg] using
    hsecond χ hχ hc hs

end ArtinMatthews
