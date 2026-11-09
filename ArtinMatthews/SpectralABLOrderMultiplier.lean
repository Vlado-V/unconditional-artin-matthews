module

public import ArtinMatthews.SpectralABLMultiplierReality
public import ArtinMatthews.SpectralBesselRightHalfPlane


set_option backward.privateInPublic true
@[expose] public section

/-! The source energy parameter and the actual ambient Bessel order
give the same even multiplier, without a branch convention assumption. -/

noncomputable section
open Set
namespace ArtinMatthews

theorem spectralEven_eq_of_square_eq (F : ℂ → ℂ) (he : ∀ z, F (-z) = F z)
    (z w : ℂ) (hs : z^2 = w^2) : F z = F w := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · rw [h]
  · rw [h,he]

theorem spectralSourceParameter_order_square (l : ℝ) :
    (spectralSourceParameter l)^2 = ((-Complex.I)*Complex.sqrt (1/4-(l : ℂ)))^2 := by
  rw [spectralSourceParameter_sq,mul_pow,neg_sq,Complex.I_sq,spectralComplexSqrt_sq]
  ring

theorem spectralABLRegularEnergyTest_order (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ)
    (l : Ici (0 : ℝ)) :
    spectralABLRegularEnergyTest T Δ hT hΔ l =
      spectralABLRegularCorrected T Δ ((-Complex.I)*Complex.sqrt (1/4-((l : ℝ) : ℂ))) := by
  rw [spectralABLRegularEnergyTest_apply]
  exact spectralEven_eq_of_square_eq _ (spectralABLRegularCorrected_even T Δ) _ _
    (spectralSourceParameter_order_square l)

theorem spectralABLExceptionalEnergyTest_order (a : ℝ) (A : ℕ) (hA : 1 ≤ A)
    (l : Ici (0 : ℝ)) :
    spectralABLExceptionalEnergyTest a A hA l =
      spectralABLExceptionalCorrected a A ((-Complex.I)*Complex.sqrt (1/4-((l : ℝ) : ℂ))) := by
  rw [spectralABLExceptionalEnergyTest_apply]
  exact spectralEven_eq_of_square_eq _ (spectralABLExceptionalCorrected_even a A) _ _
    (spectralSourceParameter_order_square l)

end ArtinMatthews
