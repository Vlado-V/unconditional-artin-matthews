module

public import ArtinMatthews.SpectralCuspExceptionalMoment
public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralAmbientBesselAmplitude
public import ArtinMatthews.SpectralBesselRightHalfPlane
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import ArtinMatthews.SpectralCuspFiniteChartMean
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralMixedCuspNormalization
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical 1/N matrix lies in Gamma0(N). Its completed native
Fourier projection and actual Bessel amplitude therefore agree with infinity. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0CuspOneOver_mem_Gamma0 (N : ℕ) :
    gamma0CuspOneOver N ∈ CongruenceSubgroup.Gamma0 N := by
  have hentry : gamma0CuspOneOver N 1 0 = -(N : ℤ) := by simp [gamma0CuspOneOver]
  rw [CongruenceSubgroup.Gamma0_mem, hentry]
  simp

theorem gamma0CuspFourierCoefficient_oneOver_eq_identity (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) :
    gamma0CuspFourierCoefficient N (gamma0CuspOneOver N) Y hY n =
      gamma0CuspFourierCoefficient N 1 Y hY n := by
  have hchart : (QuotientGroup.mk (gamma0CuspOneOver N) :
      SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) = QuotientGroup.mk (1 : SL(2, ℤ)) := by
    apply QuotientGroup.eq.mpr
    simpa only [mul_one] using (CongruenceSubgroup.Gamma0 N).inv_mem
      (gamma0CuspOneOver_mem_Gamma0 N)
  apply ContinuousLinearMap.ext
  intro f
  have hmass : gamma0CuspMassRestriction N (gamma0CuspOneOver N) Y hY f =
      gamma0CuspMassRestriction N 1 Y hY f := by
    rw [gamma0CuspMassRestriction_eq_finiteChart N (gamma0CuspOneOver N) Y hY f,
      gamma0CuspMassRestriction_eq_finiteChart N 1 Y hY f, hchart]
  simp only [gamma0CuspFourierCoefficient, ContinuousLinearMap.comp_apply, hmass]

theorem gamma0CuspBesselAmplitude_oneOver_eq_identity (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    gamma0CuspBesselAmplitude N i (gamma0CuspOneOver N) Y hY n hn =
      gamma0CuspBesselAmplitude N i 1 Y hY n hn := by
  let ν := Complex.sqrt (1 / 4 - (gamma0AllHeightGradientSpectralValue N i : ℂ))
  let q := |cuspFourierFrequency (N : ℝ) n|
  have hν : -1 / 2 < ν.re := lt_of_lt_of_le (by norm_num) (spectralComplexSqrt_re_nonneg _)
  have hq : 0 < q := abs_pos.mpr
    (cuspFourierFrequency_ne_zero (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n hn)
  apply gamma0CuspBessel_coefficient_unique N 1 n (gamma0FullCuspidalSpectralBasis N i).val
    ν hν q hq Y Y hY hY
  · rw [← gamma0CuspFourierCoefficient_oneOver_eq_identity N Y hY n]
    exact gamma0CuspBesselAmplitude_fourier_ae N i (gamma0CuspOneOver N) Y hY n hn
  · exact gamma0CuspBesselAmplitude_fourier_ae N i 1 Y hY n hn

private theorem infinity_oneOver_width (N : ℕ) [NeZero N] :
    gamma0CuspTrueWidth N (gamma0CuspOneOver N) = 1 := by
  simpa only [one_mul] using gamma0MixedCusp_trueWidth 1 N (Nat.coprime_one_left N)

theorem gamma0CuspBesselAmplitude_oneOver_trueFrequency_eq_identity (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    gamma0CuspBesselAmplitude N i (gamma0CuspOneOver N) Y hY
      ((gamma0CuspFrequencyStep N (gamma0CuspOneOver N) : ℤ)*n)
      (gamma0CuspFrequencyStep_mul_ne_zero N (gamma0CuspOneOver N) hn) =
    gamma0CuspBesselAmplitude N i 1 Y hY ((gamma0CuspFrequencyStep N 1 : ℤ)*n)
      (gamma0CuspFrequencyStep_mul_ne_zero N 1 hn) := by
  have hs₁ : gamma0CuspFrequencyStep N (gamma0CuspOneOver N) = N := by
    simpa only [infinity_oneOver_width N, one_mul] using
      gamma0CuspFrequencyStep_mul_width N (gamma0CuspOneOver N)
  have hs₂ : gamma0CuspFrequencyStep N (1 : SL(2, ℤ)) = N := by
    simpa only [gamma0CuspTrueWidth_identity, one_mul] using
      gamma0CuspFrequencyStep_mul_width N (1 : SL(2, ℤ))
  have he : ((gamma0CuspFrequencyStep N (gamma0CuspOneOver N) : ℤ)*n) =
      ((gamma0CuspFrequencyStep N 1 : ℤ)*n) := by rw [hs₁, hs₂]
  have hindex (m₁ m₂ : ℤ) (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) (hm : m₁ = m₂) :
      gamma0CuspBesselAmplitude N i 1 Y hY m₁ hm₁ =
        gamma0CuspBesselAmplitude N i 1 Y hY m₂ hm₂ := by
    subst m₂
    rfl
  exact (gamma0CuspBesselAmplitude_oneOver_eq_identity N i Y hY _ _).trans
    (hindex _ _ _ _ he)

theorem gamma0CuspExceptionalMoment_oneOver_eq_identity (N : ℕ) [NeZero N]
    (u : Finset (Gamma0AllHeightSpectralIndex N)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) (A : ℝ) :
    gamma0CuspExceptionalMoment N u (gamma0CuspOneOver N) Y hY n hn A =
      gamma0CuspExceptionalMoment N u 1 Y hY n hn A := by
  simp only [gamma0CuspExceptionalMoment, infinity_oneOver_width N, gamma0CuspTrueWidth_identity,
    Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, one_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun z : ℂ => A ^ (-2 * Real.sqrt (1 / 4 - gamma0AllHeightGradientSpectralValue N i)) * ‖z‖ ^ 2)
    (gamma0CuspBesselAmplitude_oneOver_trueFrequency_eq_identity N i Y hY n hn)

end ArtinMatthews
