module

public import ArtinMatthews.SpectralPrimitiveContinuousFourier
public import ArtinMatthews.SpectralPrimitiveWeightedPairing


set_option backward.privateInPublic true
@[expose] public section

/-! The actual bounded energy-test pairing, with its continuous term
expressed through the derived arithmetic amplitudes and K transforms.
The literal cuspidal and finite residual terms are retained. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

def gamma0WeightedContinuousFourierIntegrand (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (t : ℝ) : ℂ :=
  spectralContinuousTestSymbol h t*
    ((gamma0PrimitiveKTransform N r Y m ρ (eisensteinCriticalPoint t)*
      star (gamma0PrimitiveKTransform N b Y n η (eisensteinCriticalPoint t))*
        gamma0PrimitiveContinuousFourierKernel N r b Y hY m n hm hn t)/((2*Real.pi : ℝ) : ℂ))

theorem gamma0WeightedContinuousFourierIntegrand_ae (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    (fun t => spectralContinuousTestSymbol h t*gamma0PrimitiveEisensteinProduct N r b Y hY m n ρ η t)
      =ᵐ[volume] gamma0WeightedContinuousFourierIntegrand N h r b Y hY m n hm hn ρ η := by
  filter_upwards [gamma0PrimitiveEisensteinProduct_fourier_ae N r b Y hY m n hm hn
    ρ η hρ hη hcρ hcη hsρ hsη] with t ht
  exact congrArg (fun z : ℂ => spectralContinuousTestSymbol h t*z) ht

theorem gamma0WeightedContinuousFourierIntegrand_integrable (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    IntegrableOn (gamma0WeightedContinuousFourierIntegrand N h r b Y hY m n hm hn ρ η) (Ioi 0) := by
  apply (gamma0PrimitiveFourier_test_continuous_integrable N h r b Y hY m n
    ρ η hρ hη hcρ hcη hpρ hpη hsρ hsη).congr
  exact ae_restrict_of_ae (gamma0WeightedContinuousFourierIntegrand_ae N h r b Y hY m n hm hn
    ρ η hρ hη hcρ hcη hsρ hsη)

theorem gamma0PrimitiveFourier_weighted_continuous_fourier_pair (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    inner ℂ (gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ)
      (gamma0ContinuousTestOperator N h (gamma0PrimitiveFourierPoincareTest N b n η hη hcη hpη)) =
      ∫ t in Ioi 0,gamma0WeightedContinuousFourierIntegrand N h r b Y hY m n hm hn ρ η t := by
  rw [gamma0PrimitiveFourier_test_continuous_pair N h r b Y hY m n
    ρ η hρ hη hcρ hcη hpρ hpη hsρ hsη]
  exact integral_congr_ae (ae_restrict_of_ae (gamma0WeightedContinuousFourierIntegrand_ae N h r b Y hY m n hm hn
    ρ η hρ hη hcρ hcη hsρ hsη))

theorem gamma0PrimitiveFourier_weighted_fourier_pairing (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    let u := gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ
    let v := gamma0PrimitiveFourierPoincareTest N b n η hη hcη hpη
    inner ℂ u (gamma0AmbientTestOperator N h v) =
      (∑' i : Gamma0AllHeightSpectralIndex N,gamma0CuspidalTestSymbol N h i*
        (gamma0PrimitiveFourierSpectralCoefficient N i r Y hY m hm ρ*
          star (gamma0PrimitiveFourierSpectralCoefficient N i b Y hY n hn η)))+
      ((∫ t in Ioi 0,gamma0WeightedContinuousFourierIntegrand N h r b Y hY m n hm hn ρ η t)+
        ∑ l∈gamma0ResidualEnergyWindow N,h l*
          ∑ j,inner ℂ u (gamma0ResidualEigenbasis N l j).val*
            inner ℂ (gamma0ResidualEigenbasis N l j).val v) := by
  have he := gamma0PrimitiveFourier_test_pairing N h r b Y hY m n hm hn
    ρ η hρ hη hcρ hcη hpρ hpη hsρ hsη
  have hi : (∫ t in Ioi 0,spectralContinuousTestSymbol h t*gamma0PrimitiveEisensteinProduct N r b Y hY m n ρ η t) =
      ∫ t in Ioi 0,gamma0WeightedContinuousFourierIntegrand N h r b Y hY m n hm hn ρ η t :=
    integral_congr_ae (ae_restrict_of_ae (gamma0WeightedContinuousFourierIntegrand_ae N h r b Y hY m n hm hn
      ρ η hρ hη hcρ hcη hsρ hsη))
  dsimp only at he ⊢
  rw [hi] at he
  exact he

end ArtinMatthews
