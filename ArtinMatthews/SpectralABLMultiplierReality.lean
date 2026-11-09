module

public import ArtinMatthews.SpectralABLEnergyWindows


set_option backward.privateInPublic true
@[expose] public section

/-! Conjugation of the literal corrected windows and their values on
the full nonnegative energy axis, including complementary and zero energy. -/

noncomputable section
open Set
namespace ArtinMatthews

theorem spectralABLCoshCancellation_conj (z : ℂ) :
    star (spectralABLCoshCancellation z) = spectralABLCoshCancellation (star z) := by
  have hg (u : ℂ) : star (Complex.Gamma u) = Complex.Gamma (star u) :=
    (Complex.Gamma_conj u).symm
  have hp : star ((3/2 : ℂ)+Complex.I*z) = (3/2 : ℂ)-Complex.I*star z := by
    simp
    ring
  have hm : star ((3/2 : ℂ)-Complex.I*z) = (3/2 : ℂ)+Complex.I*star z := by
    simp
  unfold spectralABLCoshCancellation
  rw [star_div₀,star_mul,hg,hg,hp,hm]
  simp

theorem spectralABLRegularBase_conj (T Δ : ℝ) (z : ℂ) :
    star (spectralABLRegularBase T Δ z) = spectralABLRegularBase T Δ (star z) := by
  simp [spectralABLRegularBase,← Complex.exp_conj]

theorem spectralABLExceptionalBase_conj (a : ℝ) (A : ℕ) (z : ℂ) :
    star (spectralABLExceptionalBase a A z) = spectralABLExceptionalBase a A (star z) := by
  simp [spectralABLExceptionalBase,← Complex.cos_conj,map_ofNat]

theorem spectralABLRegularCorrected_conj (T Δ : ℝ) (z : ℂ) :
    star (spectralABLRegularCorrected T Δ z) = spectralABLRegularCorrected T Δ (star z) := by
  simp only [spectralABLRegularCorrected,star_mul,spectralABLRegularBase_conj,spectralABLCoshCancellation_conj]
  ring

theorem spectralABLExceptionalCorrected_conj (a : ℝ) (A : ℕ) (z : ℂ) :
    star (spectralABLExceptionalCorrected a A z) = spectralABLExceptionalCorrected a A (star z) := by
  simp only [spectralABLExceptionalCorrected,star_mul,spectralABLExceptionalBase_conj,spectralABLCoshCancellation_conj]
  ring

theorem spectralEvenConjugate_real_of_square_real (F : ℂ → ℂ)
    (hc : ∀ z, star (F z) = F (star z)) (he : ∀ z, F (-z) = F z)
    (z : ℂ) (hz : (z^2).im = 0) : star (F z) = F z := by
  rw [hc]
  have hp : z.re*z.im = 0 := by
    simp only [pow_two,Complex.mul_im] at hz
    nlinarith
  rcases mul_eq_zero.mp hp with hr | hi
  · have hs : star z = -z := by apply Complex.ext <;> simp [hr]
    rw [hs,he]
  · have hs : star z = z := by apply Complex.ext <;> simp [hi]
    rw [hs]

theorem spectralABLRegularEnergyTest_real (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ)
    (l : Ici (0 : ℝ)) :
    star (spectralABLRegularEnergyTest T Δ hT hΔ l) = spectralABLRegularEnergyTest T Δ hT hΔ l := by
  simp only [spectralABLRegularEnergyTest_apply]
  apply spectralEvenConjugate_real_of_square_real _ (spectralABLRegularCorrected_conj T Δ)
    (spectralABLRegularCorrected_even T Δ)
  rw [spectralSourceParameter_sq]
  simp

theorem spectralABLExceptionalEnergyTest_real (a : ℝ) (A : ℕ) (hA : 1 ≤ A)
    (l : Ici (0 : ℝ)) :
    star (spectralABLExceptionalEnergyTest a A hA l) = spectralABLExceptionalEnergyTest a A hA l := by
  simp only [spectralABLExceptionalEnergyTest_apply]
  apply spectralEvenConjugate_real_of_square_real _ (spectralABLExceptionalCorrected_conj a A)
    (spectralABLExceptionalCorrected_even a A)
  rw [spectralSourceParameter_sq]
  simp

theorem spectralABLRegularKuznetsovEnergyTest_real (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ)
    (l : Ici (0 : ℝ)) :
    star (spectralABLRegularKuznetsovEnergyTest T Δ hT hΔ l) =
      spectralABLRegularKuznetsovEnergyTest T Δ hT hΔ l := by
  change star ((1/4 : ℂ)*spectralABLRegularEnergyTest T Δ hT hΔ l) =
    (1/4 : ℂ)*spectralABLRegularEnergyTest T Δ hT hΔ l
  rw [star_mul,spectralABLRegularEnergyTest_real]
  norm_num
  ring

theorem spectralABLExceptionalKuznetsovEnergyTest_real (a : ℝ) (A : ℕ) (hA : 1 ≤ A)
    (l : Ici (0 : ℝ)) :
    star (spectralABLExceptionalKuznetsovEnergyTest a A hA l) =
      spectralABLExceptionalKuznetsovEnergyTest a A hA l := by
  change star ((1/4 : ℂ)*spectralABLExceptionalEnergyTest a A hA l) =
    (1/4 : ℂ)*spectralABLExceptionalEnergyTest a A hA l
  rw [star_mul,spectralABLExceptionalEnergyTest_real]
  norm_num
  ring

end ArtinMatthews
