module

public import ArtinMatthews.SpectralABLNativeRho
public import ArtinMatthews.SpectralBesselRightHalfPlane
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
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
public import Mathlib.RingTheory.SimpleRing.Principal
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


set_option backward.privateInPublic true
@[expose] public section

/-! Uniqueness of the source coefficient in the actual nonzero Fourier
mode, from the proved nonzero K solution on each positive ray. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0ABLSourceRho_unique (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (c : ℂ)
    (hc : gamma0CuspFourierCoefficient N r Y hY ((gamma0CuspFrequencyStep N r : ℤ)*n)
      (gamma0FullCuspidalSpectralBasis N i).val =ᵐ[volume.restrict (Ioi Y)] fun y =>
        c*spectralABLWhittakerZero (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ)))
          (4*Real.pi*|(n : ℝ)| *y/(gamma0CuspTrueWidth N r : ℝ))) :
    c = gamma0ABLSourceRho N i r Y hY n hn := by
  let ν := Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ))
  let w : ℝ := gamma0CuspTrueWidth N r
  let q : ℝ := |(n : ℝ)|/w
  have hw : 0 < w := by dsimp only [w];exact_mod_cast gamma0CuspTrueWidth_pos N r
  have hnR : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have hq : 0 < q := div_pos hnR hw
  have hν : -1/2 < ν.re := lt_of_lt_of_le (by norm_num) (spectralComplexSqrt_re_nonneg _)
  have hconvert (a : ℂ)
      (ha : gamma0CuspFourierCoefficient N r Y hY ((gamma0CuspFrequencyStep N r : ℤ)*n)
        (gamma0FullCuspidalSpectralBasis N i).val =ᵐ[volume.restrict (Ioi Y)] fun y =>
          a*spectralABLWhittakerZero ν (4*Real.pi*|(n : ℝ)| *y/w)) :
      gamma0CuspFourierCoefficient N r Y hY ((gamma0CuspFrequencyStep N r : ℤ)*n)
        (gamma0FullCuspidalSpectralBasis N i).val =ᵐ[volume.restrict (Ioi Y)] fun y =>
          (a*(2*Real.sqrt q : ℂ))*cuspBesselKernel ν (2*Real.pi*q) y := by
    filter_upwards [ha,ae_restrict_mem measurableSet_Ioi] with y hy hyY
    rw [hy,show 4*Real.pi*|(n : ℝ)| *y/w = 4*Real.pi*q*y by dsimp only [q];ring,
      spectralABLWhittakerZero_fourier ν q y hq (hY.trans hyY)]
    ring
  have ha := hconvert c hc
  have hb := hconvert (gamma0ABLSourceRho N i r Y hY n hn)
    (gamma0ABLSourceRho_fourier_ae N i r Y hY n hn)
  have he := gamma0CuspBessel_coefficient_unique N r ((gamma0CuspFrequencyStep N r : ℤ)*n)
    (gamma0FullCuspidalSpectralBasis N i).val ν hν (2*Real.pi*q) (by positivity)
    Y Y hY hY _ _ ha hb
  have hs : (Real.sqrt q : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hq).ne'
  exact mul_right_cancel₀ (mul_ne_zero (by norm_num) hs) he

theorem gamma0ABLSourceRho_height_eq (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (r : SL(2, ℤ)) (Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (n : ℤ) (hn : n ≠ 0) :
    gamma0ABLSourceRho N i r Y₁ hY₁ n hn = gamma0ABLSourceRho N i r Y₂ hY₂ n hn := by
  have hq : 0 < |cuspFourierFrequency (N : ℝ) ((gamma0CuspFrequencyStep N r : ℤ)*n)| :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero _ (Nat.cast_pos.mpr (NeZero.pos N)) _
      (gamma0CuspFrequencyStep_mul_ne_zero N r hn))
  have he := gamma0CuspBessel_coefficient_unique N r ((gamma0CuspFrequencyStep N r : ℤ)*n)
    (gamma0FullCuspidalSpectralBasis N i).val
    (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ)))
    (lt_of_lt_of_le (by norm_num) (spectralComplexSqrt_re_nonneg _)) _ hq Y₁ Y₂ hY₁ hY₂ _ _
    (gamma0CuspBesselAmplitude_fourier_ae N i r Y₁ hY₁ _ (gamma0CuspFrequencyStep_mul_ne_zero N r hn))
    (gamma0CuspBesselAmplitude_fourier_ae N i r Y₂ hY₂ _ (gamma0CuspFrequencyStep_mul_ne_zero N r hn))
  unfold gamma0ABLSourceRho
  rw [he]

end ArtinMatthews
