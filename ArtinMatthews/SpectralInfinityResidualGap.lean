module

public import ArtinMatthews.SpectralMixedCuspResidualGap
public import ArtinMatthews.SpectralInfinityCuspAmplitude


set_option backward.privateInPublic true
@[expose] public section

/-! The same actual ambient nonzero-mode gap holds at infinity.
Zero-energy residual vectors therefore have zero nonzero Fourier terms. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0AmbientBesselAmplitude_oneOver_eq_identity
    (N : ℕ) [NeZero N] (eig : ℝ) (heig : 0 ≤ eig) (v : Gamma0RegionL2 N)
    (hG : gamma0Green N v = (((eig+1)⁻¹ : ℝ) : ℂ) • v) (n : ℤ) (hn : n ≠ 0) :
    gamma0AmbientBesselAmplitude N eig heig v hG (gamma0CuspOneOver N) n hn =
      gamma0AmbientBesselAmplitude N eig heig v hG 1 n hn := by
  let ν := Complex.sqrt (1/4-(eig : ℂ))
  let q := |cuspFourierFrequency (N : ℝ) n|
  have hν : -1/2 < ν.re := lt_of_lt_of_le (by norm_num) (spectralComplexSqrt_re_nonneg _)
  have hq : 0 < q := abs_pos.mpr
    (cuspFourierFrequency_ne_zero (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n hn)
  apply gamma0CuspBessel_coefficient_unique N 1 n v ν hν q hq 1 1 one_pos one_pos
  · rw [← gamma0CuspFourierCoefficient_oneOver_eq_identity N 1 one_pos n]
    exact gamma0AmbientBesselAmplitude_fourier_ae N eig heig v hG (gamma0CuspOneOver N) n hn 1 one_pos
  · exact gamma0AmbientBesselAmplitude_fourier_ae N eig heig v hG 1 n hn 1 one_pos

theorem gamma0AmbientBesselAmplitude_oneOver_trueFrequency_eq_identity
    (N : ℕ) [NeZero N] (eig : ℝ) (heig : 0 ≤ eig) (v : Gamma0RegionL2 N)
    (hG : gamma0Green N v = (((eig+1)⁻¹ : ℝ) : ℂ) • v) (n : ℤ) (hn : n ≠ 0) :
    gamma0AmbientBesselAmplitude N eig heig v hG (gamma0CuspOneOver N)
      ((gamma0CuspFrequencyStep N (gamma0CuspOneOver N) : ℤ)*n)
      (gamma0CuspFrequencyStep_mul_ne_zero N (gamma0CuspOneOver N) hn) =
    gamma0AmbientBesselAmplitude N eig heig v hG 1 ((gamma0CuspFrequencyStep N 1 : ℤ)*n)
      (gamma0CuspFrequencyStep_mul_ne_zero N 1 hn) := by
  have hw : gamma0CuspTrueWidth N (gamma0CuspOneOver N) = 1 := by
    simpa only [one_mul] using gamma0MixedCusp_trueWidth 1 N (Nat.coprime_one_left N)
  have hs₁ : gamma0CuspFrequencyStep N (gamma0CuspOneOver N) = N := by
    simpa only [hw,one_mul] using gamma0CuspFrequencyStep_mul_width N (gamma0CuspOneOver N)
  have hs₂ : gamma0CuspFrequencyStep N (1 : SL(2, ℤ)) = N := by
    simpa only [gamma0CuspTrueWidth_identity,one_mul] using
      gamma0CuspFrequencyStep_mul_width N (1 : SL(2, ℤ))
  have he : ((gamma0CuspFrequencyStep N (gamma0CuspOneOver N) : ℤ)*n) =
      ((gamma0CuspFrequencyStep N 1 : ℤ)*n) := by rw [hs₁,hs₂]
  have hindex (m₁ m₂ : ℤ) (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) (hm : m₁ = m₂) :
      gamma0AmbientBesselAmplitude N eig heig v hG 1 m₁ hm₁ =
        gamma0AmbientBesselAmplitude N eig heig v hG 1 m₂ hm₂ := by
    subst m₂
    rfl
  exact (gamma0AmbientBesselAmplitude_oneOver_eq_identity N eig heig v hG _ _).trans
    (hindex _ _ _ _ he)

theorem gamma0Infinity_ambient_unit_value_ge_three_sixteenths_of_amplitude
    (N : ℕ) [NeZero N] (eig : ℝ) (heig : 0 ≤ eig) (v : Gamma0RegionL2 N)
    (hG : gamma0Green N v = (((eig+1)⁻¹ : ℝ) : ℂ) • v) (hv : ‖v‖ = 1)
    (n : ℤ) (hn : n ≠ 0)
    (hAmp : gamma0AmbientBesselAmplitude N eig heig v hG 1
      ((gamma0CuspFrequencyStep N 1 : ℤ)*n)
      (gamma0CuspFrequencyStep_mul_ne_zero N 1 hn) ≠ 0) :
    3/16 ≤ eig := by
  have h (M : ℕ) [NeZero M] (hM : M = 1*N) (u : Gamma0RegionL2 M)
      (hGu : gamma0Green M u = (((eig+1)⁻¹ : ℝ) : ℂ) • u) (hu : ‖u‖ = 1)
      (hU : gamma0AmbientBesselAmplitude M eig heig u hGu 1
        ((gamma0CuspFrequencyStep M 1 : ℤ)*n)
        (gamma0CuspFrequencyStep_mul_ne_zero M 1 hn) ≠ 0) : 3/16 ≤ eig := by
    subst M
    have hm (b : SL(2, ℤ)) (hb : b = gamma0CuspOneOver (1*N)) :
        gamma0AmbientBesselAmplitude (1*N) eig heig u hGu b
          ((gamma0CuspFrequencyStep (1*N) b : ℤ)*n)
          (gamma0CuspFrequencyStep_mul_ne_zero (1*N) b hn) ≠ 0 := by
      subst b
      rw [gamma0AmbientBesselAmplitude_oneOver_trueFrequency_eq_identity (1*N) eig heig u hGu n hn]
      exact hU
    exact gamma0MixedCusp_ambient_unit_value_ge_three_sixteenths_of_amplitude
      1 N (Nat.coprime_one_left N) eig heig u hGu hu n hn
      (hm (gamma0CuspOneOver N) (by rw [one_mul]))
  exact h N (one_mul N).symm v hG hv hAmp

theorem gamma0Infinity_residual_value_ge_three_sixteenths_of_rho
    (N : ℕ) [NeZero N] (l : Ici (0 : ℝ))
    (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l)))
    (n : ℤ) (hn : n ≠ 0) (hRho : gamma0ResidualABLSourceRho N l j 1 n hn ≠ 0) :
    3/16 ≤ (l : ℝ) := by
  let v := (gamma0ResidualEigenbasis N l j).val
  have hv : ‖v‖ = 1 := (gamma0ResidualEigenbasis N l).orthonormal.norm_eq_one j
  apply gamma0Infinity_ambient_unit_value_ge_three_sixteenths_of_amplitude N
    (l : ℝ) l.property v (gamma0ResidualEigenbasis_green N l j) hv n hn
  intro h
  apply hRho
  exact (congrArg
    (spectralABLRhoFromNative (gamma0CuspTrueWidth N 1 : ℝ) |(n : ℝ)|) h).trans
      (by simp [spectralABLRhoFromNative])

theorem gamma0Infinity_residual_zero_energy_rho (N : ℕ) [NeZero N]
    (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N 0)))
    (n : ℤ) (hn : n ≠ 0) :
    gamma0ResidualABLSourceRho N ⟨0,Set.mem_Ici.mpr le_rfl⟩ j 1 n hn = 0 := by
  by_contra h
  have hp := gamma0Infinity_residual_value_ge_three_sixteenths_of_rho N ⟨0,Set.mem_Ici.mpr le_rfl⟩ j n hn h
  norm_num at hp

end ArtinMatthews
