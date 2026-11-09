module

public import ArtinMatthews.SpectralEisensteinPhasedRow
public import ArtinMatthews.SpectralCuspEisensteinIntegral
public import ArtinMatthews.SpectralCuspEisensteinSigns


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute Fourier testing of the actual all-cusp Eisenstein row family.
The original source-width factor and the central one-half are retained. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

def cuspEisensteinRowFourierIntegral (N : ℕ) [NeZero N] (r a : SL(2, ℤ))
    (s : ℂ) (n : ℤ) (y : ℝ) (hy : 0 < y) (v : Gamma0CuspEisensteinRows N r a) : ℂ :=
  ∫ x in Ioc (0 : ℝ) 1, cuspEisensteinRowTerm N r a s v
    (cuspEisensteinTargetPoint N r y hy x)*spectralRealFourierPhase (n : ℝ) x

theorem cuspEisensteinRowFourier_horizontal_integrable (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (s : ℂ) (hs : 1 < s.re) (n : ℤ)
    (y : ℝ) (hy : 0 < y) (v : Gamma0CuspEisensteinRows N r a) :
    IntegrableOn (fun x => cuspEisensteinRowTerm N r a s v
      (cuspEisensteinTargetPoint N r y hy x)*spectralRealFourierPhase (n : ℝ) x) (Ioc (0 : ℝ) 1) := by
  have h := cuspEisensteinRowTerm_horizontal_integrable N r a s hs y hy v
  have hP : Continuous (spectralRealFourierPhase (n : ℝ)) := by
    unfold spectralRealFourierPhase
    fun_prop
  apply h.norm.mono'
  · exact h.aestronglyMeasurable.mul hP.aestronglyMeasurable
  · exact ae_of_all _ fun x => by rw [norm_mul,spectralRealFourierPhase_norm,mul_one]

theorem cuspEisensteinRowFourierIntegral_norm_summable (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (s : ℂ) (hs : 1 < s.re) (n : ℤ) (y : ℝ) (hy : 0 < y) :
    Summable (fun v : Gamma0CuspEisensteinRows N r a => ∫ x in Ioc (0 : ℝ) 1,
      ‖cuspEisensteinRowTerm N r a s v (cuspEisensteinTargetPoint N r y hy x)*
        spectralRealFourierPhase (n : ℝ) x‖) := by
  apply (cuspEisensteinRowIntegral_norm_summable N r a s hs y hy).congr
  intro v
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    rw [norm_mul,spectralRealFourierPhase_norm,mul_one]

theorem cuspEisensteinRowFourierIntegral_summable (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (s : ℂ) (hs : 1 < s.re) (n : ℤ) (y : ℝ) (hy : 0 < y) :
    Summable (cuspEisensteinRowFourierIntegral N r a s n y hy) :=
  (cuspEisensteinRowFourierIntegral_norm_summable N r a s hs n y hy).of_norm_bounded
    (f := cuspEisensteinRowFourierIntegral N r a s n y hy)
    (fun _ => norm_integral_le_integral_norm _)

theorem gamma0CuspEisenstein_fourier_integral_rows (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (s : ℂ) (hs : 1 < s.re) (n : ℤ) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, gamma0CuspEisenstein N a s
      (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y hy x)*
        spectralRealFourierPhase (n : ℝ) x) =
      (gamma0CuspTrueWidth N a : ℂ)^(-s)*(1/2 : ℂ)*
        ∑' v : Gamma0CuspEisensteinRows N r a, cuspEisensteinRowFourierIntegral N r a s n y hy v := by
  let A : ℂ := (gamma0CuspTrueWidth N a : ℂ)^(-s)*(1/2 : ℂ)
  have hp (x : ℝ) : gamma0CuspEisenstein N a s
      (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y hy x)*
        spectralRealFourierPhase (n : ℝ) x =
      A*(∑' v : Gamma0CuspEisensteinRows N r a,
        cuspEisensteinRowTerm N r a s v (cuspEisensteinTargetPoint N r y hy x)*
          spectralRealFourierPhase (n : ℝ) x) := by
    rw [gamma0CuspEisenstein_target_scaling,cuspEisensteinRowSum,tsum_mul_right]
    dsimp only [A,cuspEisensteinTargetPoint]
    ring
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp_rw [hp]
  rw [integral_const_mul,← integral_tsum_of_summable_integral_norm
    (cuspEisensteinRowFourier_horizontal_integrable N r a s hs n y hy)
    (cuspEisensteinRowFourierIntegral_norm_summable N r a s hs n y hy)]
  rfl

theorem cuspEisensteinRowFourierIntegral_neg (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (s : ℂ) (n : ℤ) (y : ℝ) (hy : 0 < y)
    (v : Gamma0CuspEisensteinRows N r a) :
    cuspEisensteinRowFourierIntegral N r a s n y hy (gamma0CuspEisensteinNegRow N r a v) =
      cuspEisensteinRowFourierIntegral N r a s n y hy v := by
  unfold cuspEisensteinRowFourierIntegral
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    rw [cuspEisensteinRowTerm_neg]

end ArtinMatthews

