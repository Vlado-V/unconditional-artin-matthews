module

public import ArtinMatthews.SpectralAmbientBesselAmplitude


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
