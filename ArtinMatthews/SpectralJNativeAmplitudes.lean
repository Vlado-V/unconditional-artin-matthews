module

public import ArtinMatthews.SpectralCuspPrincipalMoment
public import ArtinMatthews.SpectralBareSpectrumLimit
public import ArtinMatthews.SpectralABLContinuousRho


set_option backward.privateInPublic true
@[expose] public section

/-! The literal half-factor between source rho and primitive amplitudes. -/
namespace ArtinMatthews
open MeasureTheory Set
open scoped MatrixGroups
noncomputable section

theorem gamma0BareCuspidalAmplitude_half_unit (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (b : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    gamma0BareCuspidalAmplitude N i b Y hY n hn =
      (1 / 2 : ℂ) * gamma0CuspUnitAmplitude N i b Y hY n hn := by
  have h := spectralABLRhoFromNative_scale
    (gamma0CuspTrueWidth N b : ℝ) |(n : ℝ)|
    (abs_pos.mpr (by exact_mod_cast hn))
    (gamma0CuspBesselAmplitude N i b Y hY ((gamma0CuspFrequencyStep N b : ℤ) * n)
      (gamma0CuspFrequencyStep_mul_ne_zero N b hn))
  change (2 * (Real.sqrt |(n : ℝ)| : ℂ)) * gamma0ABLSourceRho N i b Y hY n hn =
    gamma0CuspUnitAmplitude N i b Y hY n hn at h
  unfold gamma0BareCuspidalAmplitude
  linear_combination (1 / 2 : ℂ) * h

theorem gamma0BareEisensteinSourceCoefficient_half_amplitude (N : ℕ) [NeZero N]
    (a : Gamma0EisensteinCuspClasses N) (b : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (t : ℝ) :
    gamma0BareEisensteinSourceCoefficient N a b Y hY n hn t =
      (1 / 2 : ℂ) * gamma0PrimitiveFourierAmplitude N
        (gamma0EisensteinCuspClassRepresentative N a) b Y hY n hn (eisensteinCriticalPoint t) := by
  have h := gamma0ABLEisensteinRho_scale N (gamma0EisensteinCuspClassRepresentative N a)
    b Y hY n hn (eisensteinCriticalPoint t)
  unfold gamma0BareEisensteinSourceCoefficient
  linear_combination (1 / 2 : ℂ) * h

theorem gamma0BareCuspidalAmplitude_norm_le_unit (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (b : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    ‖gamma0BareCuspidalAmplitude N i b Y hY n hn‖ ≤
      ‖gamma0CuspUnitAmplitude N i b Y hY n hn‖ := by
  rw [gamma0BareCuspidalAmplitude_half_unit, norm_mul]
  have h : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h]
  nlinarith [norm_nonneg (gamma0CuspUnitAmplitude N i b Y hY n hn)]

end
end ArtinMatthews
