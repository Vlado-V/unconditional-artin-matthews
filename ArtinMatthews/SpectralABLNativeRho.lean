module

public import ArtinMatthews.SpectralABLWhittakerConvention
public import ArtinMatthews.SpectralPrimitiveFourierPoincare
public import ArtinMatthews.SpectralAmbientBesselAmplitude


set_option backward.privateInPublic true
@[expose] public section

/-! Source rho coefficients of the actual native weight-zero eigenvectors.
The source period is one, raw period-N frequency is (N/w)*n, and the
normalizing factor is sqrt(w)/(2*sqrt(abs(n))). -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

theorem spectralABL_trueWidth_frequency (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (n : ℤ) :
    |cuspFourierFrequency (N : ℝ) ((gamma0CuspFrequencyStep N r : ℤ)*n)| =
      2*Real.pi*|(n : ℝ)|/(gamma0CuspTrueWidth N r : ℝ) := by
  have hw : (gamma0CuspTrueWidth N r : ℝ) ≠ 0 := by
    exact_mod_cast (gamma0CuspTrueWidth_pos N r).ne'
  apply (eq_div_iff hw).mpr
  rw [cuspFourierFrequency_abs_trueWidth,cuspFourierFrequency,div_one,abs_mul,abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2),abs_of_pos Real.pi_pos]

def gamma0ABLSourceRho (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) : ℂ :=
  spectralABLRhoFromNative (gamma0CuspTrueWidth N r : ℝ) |(n : ℝ)|
    (gamma0CuspBesselAmplitude N i r Y hY ((gamma0CuspFrequencyStep N r : ℤ)*n)
      (gamma0CuspFrequencyStep_mul_ne_zero N r hn))

theorem gamma0ABLSourceRho_fourier_ae (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    gamma0CuspFourierCoefficient N r Y hY ((gamma0CuspFrequencyStep N r : ℤ)*n)
      (gamma0FullCuspidalSpectralBasis N i).val =ᵐ[volume.restrict (Ioi Y)] fun y =>
        gamma0ABLSourceRho N i r Y hY n hn*
          spectralABLWhittakerZero (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ)))
            (4*Real.pi*|(n : ℝ)| *y/(gamma0CuspTrueWidth N r : ℝ)) := by
  have hw : 0 < (gamma0CuspTrueWidth N r : ℝ) := by exact_mod_cast gamma0CuspTrueWidth_pos N r
  have hnR : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  filter_upwards [gamma0CuspBesselAmplitude_fourier_ae N i r Y hY
    ((gamma0CuspFrequencyStep N r : ℤ)*n) (gamma0CuspFrequencyStep_mul_ne_zero N r hn),
    ae_restrict_mem measurableSet_Ioi] with y hy hyY
  rw [hy,spectralABL_trueWidth_frequency]
  exact spectralABLRhoFromNative_reconstruction _ _ _ _ _ hw hnR (hY.trans hyY)

theorem gamma0ABLSourceRho_norm_sq (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    ‖gamma0ABLSourceRho N i r Y hY n hn‖^2 =
      (gamma0CuspTrueWidth N r : ℝ)/(4*|(n : ℝ)|)*
        ‖gamma0CuspBesselAmplitude N i r Y hY ((gamma0CuspFrequencyStep N r : ℤ)*n)
          (gamma0CuspFrequencyStep_mul_ne_zero N r hn)‖^2 :=
  spectralABLRhoFromNative_norm_sq _ _ (by exact_mod_cast gamma0CuspTrueWidth_pos N r)
    (abs_pos.mpr (by exact_mod_cast hn)) _

theorem gamma0PrimitiveFourierSpectralCoefficient_sourceRho (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) (ρ : ℝ → ℝ) :
    gamma0PrimitiveFourierSpectralCoefficient N i r Y hY n hn ρ =
      (2*Real.sqrt |(n : ℝ)| : ℂ)*gamma0ABLSourceRho N i r Y hY n hn*
        cuspBesselTransform (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ)))
          |cuspFourierFrequency 1 n| (Y/(gamma0CuspTrueWidth N r : ℝ))
          (fun u => ρ ((gamma0CuspTrueWidth N r : ℝ)*u)) := by
  unfold gamma0PrimitiveFourierSpectralCoefficient gamma0ABLSourceRho
  rw [spectralABLRhoFromNative_scale _ _ (abs_pos.mpr (by exact_mod_cast hn))]

def gamma0AmbientABLSourceRho (N : ℕ) [NeZero N] (eig : ℝ) (hl : 0 ≤ eig)
    (m : Gamma0RegionL2 N) (hG : gamma0Green N m = (((eig+1)⁻¹ : ℝ) : ℂ) • m)
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) : ℂ :=
  spectralABLRhoFromNative (gamma0CuspTrueWidth N r : ℝ) |(n : ℝ)|
    (gamma0AmbientBesselAmplitude N eig hl m hG r ((gamma0CuspFrequencyStep N r : ℤ)*n)
      (gamma0CuspFrequencyStep_mul_ne_zero N r hn))

theorem gamma0AmbientABLSourceRho_fourier_ae (N : ℕ) [NeZero N] (eig : ℝ) (hl : 0 ≤ eig)
    (m : Gamma0RegionL2 N) (hG : gamma0Green N m = (((eig+1)⁻¹ : ℝ) : ℂ) • m)
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (Y : ℝ) (hY : 0 < Y) :
    gamma0CuspFourierCoefficient N r Y hY ((gamma0CuspFrequencyStep N r : ℤ)*n) m
      =ᵐ[volume.restrict (Ioi Y)] fun y => gamma0AmbientABLSourceRho N eig hl m hG r n hn*
        spectralABLWhittakerZero (Complex.sqrt (1/4-(eig : ℂ)))
          (4*Real.pi*|(n : ℝ)| *y/(gamma0CuspTrueWidth N r : ℝ)) := by
  have hw : 0 < (gamma0CuspTrueWidth N r : ℝ) := by exact_mod_cast gamma0CuspTrueWidth_pos N r
  have hnR : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  filter_upwards [gamma0AmbientBesselAmplitude_fourier_ae N eig hl m hG r
    ((gamma0CuspFrequencyStep N r : ℤ)*n) (gamma0CuspFrequencyStep_mul_ne_zero N r hn) Y hY,
    ae_restrict_mem measurableSet_Ioi] with y hy hyY
  rw [hy,spectralABL_trueWidth_frequency]
  exact spectralABLRhoFromNative_reconstruction _ _ _ _ _ hw hnR (hY.trans hyY)

end ArtinMatthews
