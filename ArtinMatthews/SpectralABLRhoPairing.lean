module

public import ArtinMatthews.SpectralABLContinuousRho
public import ArtinMatthews.SpectralABLEnergyWindows
public import ArtinMatthews.SpectralPrimitiveWeightedFourier


set_option backward.privateInPublic true
@[expose] public section

/-! Exact source-normalized spectral pairing. The native operator uses
one quarter of the cosh-corrected energy test. The full finite residual
sector and the literal positive-frequency dt/(2*pi) integral are retained. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

def gamma0ABLCuspTestCoefficient (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (ρ : ℝ → ℝ) : ℂ :=
  (Real.sqrt |(n : ℝ)| : ℂ)*gamma0ABLSourceRho N i r Y hY n hn*
    cuspBesselTransform (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ)))
      |cuspFourierFrequency 1 n| (Y/(gamma0CuspTrueWidth N r : ℝ))
      (fun u => ρ ((gamma0CuspTrueWidth N r : ℝ)*u))

theorem gamma0PrimitiveFourierSpectralCoefficient_twice_source (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) (ρ : ℝ → ℝ) :
    gamma0PrimitiveFourierSpectralCoefficient N i r Y hY n hn ρ =
      2*gamma0ABLCuspTestCoefficient N i r Y hY n hn ρ := by
  rw [gamma0PrimitiveFourierSpectralCoefficient_sourceRho]
  unfold gamma0ABLCuspTestCoefficient
  ring

theorem gamma0ABLCuspidal_weight_conversion (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (i : Gamma0AllHeightSpectralIndex N) (r b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (ρ η : ℝ → ℝ) :
    gamma0CuspidalTestSymbol N ((1/4 : ℂ) • h) i*
      (gamma0PrimitiveFourierSpectralCoefficient N i r Y hY m hm ρ*
        star (gamma0PrimitiveFourierSpectralCoefficient N i b Y hY n hn η)) =
      gamma0CuspidalTestSymbol N h i*(gamma0ABLCuspTestCoefficient N i r Y hY m hm ρ*
        star (gamma0ABLCuspTestCoefficient N i b Y hY n hn η)) := by
  rw [gamma0PrimitiveFourierSpectralCoefficient_twice_source,
    gamma0PrimitiveFourierSpectralCoefficient_twice_source,star_mul]
  have hh : gamma0CuspidalTestSymbol N ((1/4 : ℂ) • h) i =
      (1/4 : ℂ)*gamma0CuspidalTestSymbol N h i := rfl
  rw [hh]
  norm_num
  ring

def gamma0ABLContinuousTestIntegrand (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (t : ℝ) : ℂ :=
  spectralContinuousTestSymbol h t*
    (gamma0PrimitiveKTransform N r Y m ρ (eisensteinCriticalPoint t)*
      star (gamma0PrimitiveKTransform N b Y n η (eisensteinCriticalPoint t))*
        (Real.sqrt |(m : ℝ)| : ℂ)*(Real.sqrt |(n : ℝ)| : ℂ)*
          gamma0ABLContinuousRhoKernel N r b Y hY m n hm hn t)/((2*Real.pi : ℝ) : ℂ)

theorem gamma0ABLContinuous_weight_conversion (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (t : ℝ) :
    gamma0WeightedContinuousFourierIntegrand N ((1/4 : ℂ) • h) r b Y hY m n hm hn ρ η t =
      gamma0ABLContinuousTestIntegrand N h r b Y hY m n hm hn ρ η t := by
  unfold gamma0WeightedContinuousFourierIntegrand gamma0ABLContinuousTestIntegrand
  rw [gamma0PrimitiveContinuousFourierKernel_sourceRho]
  have hh : spectralContinuousTestSymbol ((1/4 : ℂ) • h) t =
      (1/4 : ℂ)*spectralContinuousTestSymbol h t := rfl
  rw [hh]
  ring

theorem gamma0ABLContinuousTestIntegrand_integrable (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    IntegrableOn (gamma0ABLContinuousTestIntegrand N h r b Y hY m n hm hn ρ η) (Ioi 0) := by
  have he : gamma0WeightedContinuousFourierIntegrand N ((1/4 : ℂ) • h) r b Y hY m n hm hn ρ η =
      gamma0ABLContinuousTestIntegrand N h r b Y hY m n hm hn ρ η := by
    funext t
    exact gamma0ABLContinuous_weight_conversion N h r b Y hY m n hm hn ρ η t
  rw [← he]
  exact gamma0WeightedContinuousFourierIntegrand_integrable N ((1/4 : ℂ) • h) r b Y hY m n hm hn
    ρ η hρ hη hcρ hcη hpρ hpη hsρ hsη

theorem gamma0ABLRho_source_spectral_pairing (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    let u := gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ
    let v := gamma0PrimitiveFourierPoincareTest N b n η hη hcη hpη
    inner ℂ u (gamma0AmbientTestOperator N ((1/4 : ℂ) • h) v) =
      (∑' i : Gamma0AllHeightSpectralIndex N,gamma0CuspidalTestSymbol N h i*
        (gamma0ABLCuspTestCoefficient N i r Y hY m hm ρ*
          star (gamma0ABLCuspTestCoefficient N i b Y hY n hn η)))+
      ((∫ t in Ioi 0,gamma0ABLContinuousTestIntegrand N h r b Y hY m n hm hn ρ η t)+
        ∑ l∈gamma0ResidualEnergyWindow N,((1/4 : ℂ) • h) l*
          ∑ j,inner ℂ u (gamma0ResidualEigenbasis N l j).val*
            inner ℂ (gamma0ResidualEigenbasis N l j).val v) := by
  have he := gamma0PrimitiveFourier_weighted_fourier_pairing N ((1/4 : ℂ) • h)
    r b Y hY m n hm hn ρ η hρ hη hcρ hcη hpρ hpη hsρ hsη
  dsimp only at he ⊢
  simp_rw [gamma0ABLCuspidal_weight_conversion,gamma0ABLContinuous_weight_conversion] at he
  exact he

def spectralABLLiteralRegularEnergyTest (T ε : ℝ) (hT : 0 < T) : SpectralEnergyTest :=
  spectralABLRegularKuznetsovEnergyTest T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _)

def spectralABLLiteralExceptionalEnergyTest (a : ℝ) (A : ℕ) (hA : 1 ≤ A) : SpectralEnergyTest :=
  spectralABLExceptionalKuznetsovEnergyTest a A hA

theorem spectralABLLiteralRegularEnergyTest_continuous_symbol (T ε : ℝ) (hT : 0 < T) (t : ℝ) :
    spectralContinuousTestSymbol (spectralABLLiteralRegularEnergyTest T ε hT) t =
      spectralABLRegularWindow T (T^(1-ε)) (t : ℂ)/(4*(Real.cosh (Real.pi*t) : ℂ)) := by
  change (1/4 : ℂ)*spectralContinuousTestSymbol
    (spectralABLRegularEnergyTest T (T^(1-ε)) hT (Real.rpow_pos_of_pos hT _)) t = _
  rw [spectralABLRegularEnergyTest_continuous_symbol]
  ring

theorem spectralABLLiteralExceptionalEnergyTest_continuous_symbol (a : ℝ) (A : ℕ)
    (hA : 1 ≤ A) (t : ℝ) :
    spectralContinuousTestSymbol (spectralABLLiteralExceptionalEnergyTest a A hA) t =
      spectralABLExceptionalWindow a A (t : ℂ)/(4*(Real.cosh (Real.pi*t) : ℂ)) := by
  change (1/4 : ℂ)*spectralContinuousTestSymbol (spectralABLExceptionalEnergyTest a A hA) t = _
  rw [spectralABLExceptionalEnergyTest_continuous_symbol]
  ring

end ArtinMatthews
