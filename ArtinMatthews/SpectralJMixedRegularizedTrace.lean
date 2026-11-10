module

public import ArtinMatthews.SpectralBareModulusSeries
public import ArtinMatthews.SpectralBareSpectrumLimit
public import ArtinMatthews.SpectralJRegularizedEnergyTest
public import ArtinMatthews.SpectralBareTestDominance
public import ArtinMatthews.SpectralJNativeHeatSource
public import ArtinMatthews.SpectralJRegularizedSourceAbsolute
public import ArtinMatthews.SpectralMixedCuspInequivalent
public import ArtinMatthews.SpectralMixedJHeatTannery
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
open MeasureTheory Set Filter Complex
open scoped ContDiff MatrixGroups Topology ComplexConjugate
noncomputable section

theorem gamma0MixedJ_regularized_bare_trace_real
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (hreal : ∀ x : ℝ, conj (f x) = f x)
    (r s : ℕ) [NeZero r] [NeZero s] (hr : 1 < r) (hcop : r.Coprime s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 0 < m * n)
    (L : ℝ) (hL : 0 ≤ L) :
    gamma0BareSourceSpectralSide (r * s) (spectralJRegularizedEnergyTest f hf hc hp L hL)
      (gamma0CuspOneOver s) 1 Y hY n m hn hm =
      (1 / 4 : ℂ) * ∑' q : Ioi (0 : ℕ),
        gamma0TrueWidthBareFibre (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJRegularizedWeight f L) := by
  obtain ⟨hC, hI⟩ := gamma0JRegularizedSource_absolute_swapped
    f hf hc hp r s hcop Y hY m n hm hn L hL
  have hSpectral := gamma0HeatSourceSpectralSide_tendsto_of_bare (r * s)
    (spectralJRegularizedEnergyTest f hf hc hp L hL)
    (gamma0CuspOneOver s) 1 Y hY n m hn hm hC hI
  have hGeometric := (gamma0MixedJRegularizedHeatSeries_tendsto_bare
    f hf hc hp r s hcop m n hmn L hL).2
  apply tendsto_nhds_unique hSpectral
  apply (tendsto_const_nhds.mul hGeometric).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact (gamma0JHeatSource_inequivalent_trace (r * s)
    (gamma0CuspOneOver s) 1 (gamma0MixedCusps_inequivalent_of_one_lt r s hr)
    Y hY n m hn hm (by simpa only [mul_comm n m] using hmn)
    f hf hc hp hreal L R hL hR).symm

end
end ArtinMatthews
