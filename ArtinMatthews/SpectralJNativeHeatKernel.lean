module

public import ArtinMatthews.SpectralHeatArithmeticKernel
public import ArtinMatthews.SpectralHeatDiagonal
public import ArtinMatthews.SpectralJRegularizedWeight
public import ArtinMatthews.SpectralKLUnitary
public import ArtinMatthews.SpectralCuspHeightL2
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralHeatKLAnalysis
public import ArtinMatthews.SpectralHeatOrbitalKernel
public import ArtinMatthews.SpectralJRegularizedHeat
public import ArtinMatthews.SpectralJRegularizedWeightBounds
public import ArtinMatthews.SpectralNativeHeatMoment
public import ArtinMatthews.SpectralWeylTwoProfileKL
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
open MeasureTheory Set Filter
open scoped MatrixGroups ContDiff
noncomputable section

theorem spectralJRegularizedHeatProfile_completed_analysis
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ)) (L R : ℝ) (hL : 0 ≤ L) (hR : 0 < R)
    (hG : MemLp (spectralKLWeightedHeatProfile (spectralJRegularizedWeight f L) R)
      2 spectralKLPhysicalMeasure) :
    spectralKLAnalysis (hG.toLp (spectralKLWeightedHeatProfile (spectralJRegularizedWeight f L) R))
      =ᵐ[spectralKLSpectralMeasure] fun t : ℝ =>
        spectralKLGaussianWeightedData (spectralJRegularizedWeight f L) R (t : ℂ) := by
  obtain ⟨C, hC, hbound⟩ := spectralJRegularizedWeight_strip_bound f hf hc hs L hL
  exact spectralKLWeightedHeatProfile_completed_analysis _ R hR
    (spectralJRegularizedWeight_real_contDiff f hf.continuous hc hs L) C hC hbound hG

theorem spectralWeylJRegularizedHeat_same_J {X : ℝ} (hX : 0 < X)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (L R : ℝ) (hL : 0 ≤ L) (hR : 0 < R)
    (s t : ℝ) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (hst : s * t = 1) :
    spectralWeylPhysicalBilinear s t
      (spectralKLWeightedHeatProfile (spectralJRegularizedWeight f L) R)
      (spectralKLHeatProfile R) X =
      ∫ u, spectralWeylJMultiplier u X * spectralJRegularizedWeight f L (u : ℂ) *
        Complex.exp (-2 * ((u : ℂ) / (R : ℂ)) ^ 2) ∂spectralKLSpectralMeasure := by
  let F := spectralKLHeatProfile R
  let G := spectralKLWeightedHeatProfile (spectralJRegularizedWeight f L) R
  have hF := spectralKLHeatProfile_properties R hR
  have hG := spectralJRegularizedHeatProfile_properties f hf hc hp L R hL hR
  have hzF := spectralKLHeatProfile_nonpositive_zero R
  have hzG := spectralKLWeightedHeatProfile_nonpositive_zero (spectralJRegularizedWeight f L) R
  have hmF := spectralKLHeatRegularity_measurable F hF hzF
  have hmG := spectralKLHeatRegularity_measurable G hG hzG
  obtain ⟨M, hM, hpower⟩ := (spectralKLHeatRegularity_five_eighths G hG hzG).2
  have hMoment := (spectralKLHeatRegularity_five_eighths F hF hzF).1
  have he := spectralWeylPhysicalBilinear_same_J_two_noncompact zero_lt_one hX
    (by norm_num : (0 : ℝ) < 5 / 8) (by norm_num : (5 / 8 : ℝ) ≤ 1) hM
    s t hs ht hst G F hmG hmF hG.1.continuousOn hF.1.continuousOn
    hG.2.1 hF.2.1 hMoment hpower
  rw [he]
  apply integral_congr_ae
  filter_upwards [spectralJRegularizedHeatProfile_completed_analysis f hf hc hp L R hL hR hG.2.1,
    spectralKLHeatProfile_completed_analysis R hR hF.2.1] with u hGu hFu
  rw [hGu, hFu, spectralKLGaussianWeightedData, spectralKLGaussianData_real_star]
  calc
    _ = spectralWeylJMultiplier u X * spectralJRegularizedWeight f L (u : ℂ) *
        (spectralKLGaussianData R (u : ℂ) * spectralKLGaussianData R (u : ℂ)) := by ring
    _ = _ := by rw [spectralHeatGaussian_square]

theorem spectralWeylJRegularizedHeat_same_sign {X : ℝ} (hX : 0 < X)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (L R : ℝ) (hL : 0 ≤ L) (hR : 0 < R)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 0 < m * n) :
    spectralWeylPhysicalBilinear
      (cuspFourierFrequency 1 m / |cuspFourierFrequency 1 m|)
      (cuspFourierFrequency 1 n / |cuspFourierFrequency 1 n|)
      (spectralKLWeightedHeatProfile (spectralJRegularizedWeight f L) R)
      (spectralKLHeatProfile R) X =
        spectralABLHeatKernel (spectralJRegularizedWeight f L) R m n X := by
  have hu := cuspFourierFrequency_ne_zero 1 zero_lt_one m hm
  have hv := cuspFourierFrequency_ne_zero 1 zero_lt_one n hn
  have hprod := spectralWeyl_frequency_sign_product hu hv
  rw [ite_eq_left ((spectralWeyl_cusp_frequency_product_pos zero_lt_one m n).mpr hmn)] at hprod
  rw [spectralWeylJRegularizedHeat_same_J hX f hf hc hp L R hL hR _ _
    (spectralWeyl_frequency_sign_sq hu) (spectralWeyl_frequency_sign_sq hv) hprod]
  simp only [spectralABLHeatKernel, spectralWeylIntegerSignMultiplier, ite_eq_left hmn]

theorem gamma0TrueWidthJRegularizedHeatFibre
    (N : ℕ) [NeZero N] (r s : SL(2, ℤ)) (c : Ioi (0 : ℕ))
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 0 < m * n)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (L R : ℝ) (hL : 0 ≤ L) (hR : 0 < R) :
    gamma0TrueWidthPhysicalFibre N r s c m n
      (spectralKLWeightedHeatProfile (spectralJRegularizedWeight f L) R)
      (spectralKLHeatProfile R) =
        gamma0TrueWidthHeatFibre N r s c m n (spectralJRegularizedWeight f L) R := by
  have hm0 := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one m hm)
  have hn0 := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hC := gamma0TrueWidthModulus_pos N r s (Nat.cast_pos.mpr c.property)
  unfold gamma0TrueWidthPhysicalFibre gamma0TrueWidthHeatFibre
  dsimp only
  rw [spectralWeylJRegularizedHeat_same_sign (by positivity) f hf hc hp L R hL hR m n hm hn hmn]

theorem spectralJRegularizedHeat_inner
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (L R : ℝ) (hL : 0 ≤ L) (hR : 0 < R)
    (hF : MemLp (spectralKLHeatProfile R) 2 spectralKLPhysicalMeasure)
    (hG : MemLp (spectralKLWeightedHeatProfile (spectralJRegularizedWeight f L) R)
      2 spectralKLPhysicalMeasure) :
    inner ℂ (hF.toLp _) (hG.toLp _) =
      spectralABLHeatDiagonal (spectralJRegularizedWeight f L) R := by
  rw [← spectralKLAnalysis.inner_map_map, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [spectralKLHeatProfile_completed_analysis R hR hF,
    spectralJRegularizedHeatProfile_completed_analysis f hf hc hp L R hL hR hG] with t htF htG
  rw [htF, htG, RCLike.inner_apply]
  change spectralKLGaussianWeightedData (spectralJRegularizedWeight f L) R (t : ℂ) *
    star (spectralKLGaussianData R (t : ℂ)) = _
  rw [spectralKLGaussianWeightedData, spectralKLGaussianData_real_star]
  calc
    _ = spectralJRegularizedWeight f L (t : ℂ) *
        (spectralKLGaussianData R (t : ℂ) * spectralKLGaussianData R (t : ℂ)) := by ring
    _ = _ := by rw [spectralHeatGaussian_square]

theorem gamma0JHeat_diagonal
    (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (hreal : ∀ x : ℝ, star (f x) = f x)
    (L R : ℝ) (hL : 0 ≤ L) (hR : 0 < R) :
    (gamma0CuspTrueWidth N r : ℂ) *
      (cuspFourierHeightPairing
        (fun y => Real.sqrt (y / (gamma0CuspTrueWidth N r : ℝ)) *
          (spectralKLHeatProfile R
            ((|cuspFourierFrequency 1 n| / (gamma0CuspTrueWidth N r : ℝ)) * y)).re)
        (fun y => Real.sqrt (y / (gamma0CuspTrueWidth N r : ℝ)) *
          (spectralKLWeightedHeatProfile (spectralJRegularizedWeight f L) R
            ((|cuspFourierFrequency 1 n| / (gamma0CuspTrueWidth N r : ℝ)) * y)).re) : ℂ) =
      spectralABLHeatDiagonal (spectralJRegularizedWeight f L) R := by
  have hF := (spectralKLHeatProfile_properties R hR).2.1
  have hG := (spectralJRegularizedHeatProfile_properties f hf hc hp L R hL hR).2.1
  have hd := cuspFourierHeightPairing_dilation_inner |cuspFourierFrequency 1 n|
    (gamma0CuspTrueWidth N r : ℝ)
    (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn))
    (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)) _ _ hF hG
    (fun x _ => spectralKLHeatProfile_real R x)
    (fun x _ => spectralJRegularizedHeatProfile_real f hf.continuous hc hp hreal L R x)
  have hwidth : (((gamma0CuspTrueWidth N r : ℝ) : ℂ)) = (gamma0CuspTrueWidth N r : ℂ) := by
    norm_cast
  rw [hwidth] at hd
  exact hd.trans (spectralJRegularizedHeat_inner f hf hc hp L R hL hR hF hG)

end
end ArtinMatthews
