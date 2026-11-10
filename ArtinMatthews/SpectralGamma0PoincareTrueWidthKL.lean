module

public import ArtinMatthews.SpectralCuspTrueWidth
public import ArtinMatthews.SpectralGamma0PoincareBessel
public import ArtinMatthews.SpectralKLAnalysisIntegral
public import ArtinMatthews.SpectralKLHeightPhysicalTest
public import ArtinMatthews.SpectralGamma0PoincareKL
public import ArtinMatthews.SpectralKLCuspWidthTransform
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

/-! Exact native Poincare/KL input in true cusp coordinates. The external
factor 2*N/sqrt(width) remains literal; no noncuspidal sector is removed. -/

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff MatrixGroups

namespace ArtinMatthews

theorem gamma0FourierPoincareTest_native_trueWidth_bessel (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (j : ℤ) (hn : (gamma0CuspFrequencyStep N r : ℤ)*j ≠ 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (hs : tsupport ρ ⊆ Ioi Y) :
    inner ℂ (gamma0FourierPoincareTest N r ((gamma0CuspFrequencyStep N r : ℤ)*j) ρ hρ hcρ hpos)
      (gamma0FullCuspidalSpectralBasis N i).val =
        ((2*(N : ℂ))/(Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ))*
          gamma0CuspBesselAmplitude N i r Y hY ((gamma0CuspFrequencyStep N r : ℤ)*j) hn*
          cuspBesselTransform
            (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ)))
            |cuspFourierFrequency 1 j| (Y/(gamma0CuspTrueWidth N r : ℝ))
            (fun u => ρ ((gamma0CuspTrueWidth N r : ℝ)*u)) := by
  rw [gamma0FourierPoincareTest_native_inner N i r Y hY _ hn ρ hρ hcρ hpos hs,
    cuspBesselTransform_trueWidth N r _ j Y hY ρ]
  simp only [div_eq_mul_inv]
  ring

theorem gamma0FourierPoincareTest_native_trueWidth_principal_KL (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N)
    (heig : 1/4 ≤ gamma0AllHeightGradientSpectralValue N i) (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (j : ℤ) (hn : (gamma0CuspFrequencyStep N r : ℤ)*j ≠ 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (hs : tsupport ρ ⊆ Ioi Y) :
    inner ℂ (gamma0FourierPoincareTest N r ((gamma0CuspFrequencyStep N r : ℤ)*j) ρ hρ hcρ hpos)
      (gamma0FullCuspidalSpectralBasis N i).val =
        ((2*(N : ℂ))/(Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ))*
          gamma0CuspBesselAmplitude N i r Y hY ((gamma0CuspFrequencyStep N r : ℤ)*j) hn*
          spectralKLPhysicalAnalysisIntegral
            (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 j|
              (fun u => ρ ((gamma0CuspTrueWidth N r : ℝ)*u)))
            (Real.sqrt (gamma0AllHeightGradientSpectralValue N i-1/4)) := by
  rw [gamma0FourierPoincareTest_native_inner N i r Y hY _ hn ρ hρ hcρ hpos hs,
    spectralComplexSqrt_quarter_sub_real _ heig,
    cuspBesselTransform_trueWidth_imaginary_KL N r j (right_ne_zero_of_mul hn) Y hY
      ρ hρ.continuous hcρ hs]
  simp only [div_eq_mul_inv]
  ring

theorem gamma0FourierPoincareTest_native_trueWidth_principal_projected_KL (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N)
    (heig : 1/4 ≤ gamma0AllHeightGradientSpectralValue N i) (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (j : ℤ) (hn : (gamma0CuspFrequencyStep N r : ℤ)*j ≠ 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (hs : tsupport ρ ⊆ Ioi Y) :
    inner ℂ (gamma0CuspidalProjection N
      (gamma0FourierPoincareTest N r ((gamma0CuspFrequencyStep N r : ℤ)*j) ρ hρ hcρ hpos))
      (gamma0FullCuspidalSpectralBasis N i) =
        ((2*(N : ℂ))/(Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ))*
          gamma0CuspBesselAmplitude N i r Y hY ((gamma0CuspFrequencyStep N r : ℤ)*j) hn*
          spectralKLPhysicalAnalysisIntegral
            (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 j|
              (fun u => ρ ((gamma0CuspTrueWidth N r : ℝ)*u)))
            (Real.sqrt (gamma0AllHeightGradientSpectralValue N i-1/4)) := by
  rw [gamma0CuspidalProjection_inner_right]
  exact gamma0FourierPoincareTest_native_trueWidth_principal_KL N i heig r Y hY j hn ρ hρ hcρ hpos hs

end ArtinMatthews
