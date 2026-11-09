module

public import ArtinMatthews.SpectralGamma0PoincareKL
public import ArtinMatthews.SpectralKLCuspWidthTransform


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
