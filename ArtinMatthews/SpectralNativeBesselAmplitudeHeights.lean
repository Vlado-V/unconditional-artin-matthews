module

public import ArtinMatthews.SpectralGamma0PoincareBessel
public import ArtinMatthews.SpectralAmbientBesselAmplitude
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

/-! The chosen native cuspidal Bessel amplitude is independent of the
positive base height on the actual nested restrictions. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0CuspBesselAmplitude_height_eq (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (r : SL(2, ℤ))
    (Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (n : ℤ) (hn : n ≠ 0) :
    gamma0CuspBesselAmplitude N i r Y₁ hY₁ n hn = gamma0CuspBesselAmplitude N i r Y₂ hY₂ n hn := by
  let ν := Complex.sqrt (1 / 4 - (gamma0AllHeightGradientSpectralValue N i : ℂ))
  have hν : -1 / 2 < ν.re := lt_of_lt_of_le (by norm_num) (spectralComplexSqrt_re_nonneg _)
  have hq : 0 < |cuspFourierFrequency (N : ℝ) n| := abs_pos.mpr
    (cuspFourierFrequency_ne_zero _ (Nat.cast_pos.mpr (NeZero.pos N)) n hn)
  exact gamma0CuspBessel_coefficient_unique N r n (gamma0FullCuspidalSpectralBasis N i).val
    ν hν _ hq Y₁ Y₂ hY₁ hY₂ _ _
    (gamma0CuspBesselAmplitude_fourier_ae N i r Y₁ hY₁ n hn)
    (gamma0CuspBesselAmplitude_fourier_ae N i r Y₂ hY₂ n hn)

end ArtinMatthews
