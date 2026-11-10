module

public import ArtinMatthews.SpectralHeatKernelLimit
public import ArtinMatthews.SpectralABLBareIntegrability
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

/-! Concrete removal of the Gaussian factor from each fixed positive
argument of the source J/K kernel. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ArtinMatthews

theorem spectralABLRegularHeatKernel_tendsto (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ)
    (m n : ℤ) {X : ℝ} (hX : 0 < X) :
    Tendsto (fun R : ℝ => spectralABLHeatKernel (spectralABLRegularCorrected T Δ) R m n X) atTop
      (𝓝 (spectralABLBareKernel (spectralABLRegularCorrected T Δ) m n X)) :=
  spectralABLHeatKernel_tendsto_bare _ (spectralABLRegularCorrected_integrable T Δ hT hΔ) m n hX

theorem spectralABLExceptionalHeatKernel_tendsto (a : ℝ) (A : ℕ) (hA : 3 ≤ A)
    (m n : ℤ) {X : ℝ} (hX : 0 < X) :
    Tendsto (fun R : ℝ => spectralABLHeatKernel (spectralABLExceptionalCorrected a A) R m n X) atTop
      (𝓝 (spectralABLBareKernel (spectralABLExceptionalCorrected a A) m n X)) :=
  spectralABLHeatKernel_tendsto_bare _ (spectralABLExceptionalCorrected_integrable a A hA) m n hX

end ArtinMatthews
