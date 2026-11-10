module

public import ArtinMatthews.SpectralBareEisensteinCoefficient
public import ArtinMatthews.SpectralHeatCuspidalSplit
public import ArtinMatthews.SpectralJClippedEnergyTest
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralJContinuousMass
public import ArtinMatthews.SpectralJInfinityPrincipalMass
public import ArtinMatthews.SpectralJMixedPrincipalMass
public import ArtinMatthews.SpectralJNativeContinuousAbsolute
public import ArtinMatthews.SpectralJNativeCuspidalAbsolute
public import ArtinMatthews.SpectralJNativeHeight
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

/-! Absolute native source convergence at every positive auxiliary height. -/
namespace ArtinMatthews
open MeasureTheory Set
open scoped ContDiff MatrixGroups
noncomputable section

theorem gamma0JSource_absolute (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    Summable (fun i => ‖gamma0BareCuspidalTerm (r * s)
      (spectralJClippedEnergyTest f hf hc hp) 1 (gamma0CuspOneOver s) Y hY m n hm hn i‖) ∧
    IntegrableOn (gamma0BareContinuousRhoIntegrand (r * s)
      (spectralJClippedEnergyTest f hf hc hp) 1 (gamma0CuspOneOver s) Y hY m n hm hn) (Ioi (0 : ℝ)) := by
  let Bm := |cuspFourierFrequency 1 m|
  let Bn := |cuspFourierFrequency 1 n| /
    (gamma0CuspTrueWidth (r * s) (gamma0CuspOneOver s) : ℝ)
  have hBm : 0 < Bm := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos m hm)
  have hBn : 0 < Bn := div_pos (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn))
    (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos (r * s) (gamma0CuspOneOver s)))
  let Z := min ((1 / 32 : ℝ) / Bm) ((1 / 32 : ℝ) / Bn)
  have hZ : 0 < Z := lt_min (by positivity) (by positivity)
  have hZm : Z < (1 / 16) / Bm :=
    lt_of_le_of_lt (min_le_left _ _) (div_lt_div_of_pos_right (by norm_num) hBm)
  have hZn : Z < (1 / 16) / Bn :=
    lt_of_le_of_lt (min_le_right _ _) (div_lt_div_of_pos_right (by norm_num) hBn)
  have hD₁ := gamma0Infinity_nativePrincipal_summable (r * s) Z hZ m hm hZm
  have hD₂ := gamma0MixedCusp_nativePrincipal_summable r s hcop Z hZ n hn hZn
  have hC := gamma0JClipped_cuspidal_absolute_of_principal f hf hc hp (r * s)
    1 (gamma0CuspOneOver s) Z hZ m n hm hn hD₁ hD₂
  have hI₁ := gamma0Infinity_continuous_quartic_integrable (r * s) Z hZ m hm hZm
  have hI₂ := gamma0MixedCusp_continuous_quartic_integrable r s hcop Z hZ n hn hZn
  have hI := gamma0JClipped_continuous_absolute_of_densities f hf hc hp (r * s)
    1 (gamma0CuspOneOver s) Z hZ m n hm hn hI₁ hI₂
  constructor
  · apply hC.congr
    intro i
    rw [gamma0BareCuspidalTerm_height_eq (r * s) (spectralJClippedEnergyTest f hf hc hp)
      1 (gamma0CuspOneOver s) Z Y hZ hY m n hm hn i]
  · apply hI.congr
    exact ae_restrict_of_ae
      (gamma0BareContinuousRhoIntegrand_height_ae (r * s) (spectralJClippedEnergyTest f hf hc hp)
        1 (gamma0CuspOneOver s) Z Y hZ hY m n hm hn)

end
end ArtinMatthews
