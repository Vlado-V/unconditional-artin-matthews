module

public import ArtinMatthews.SpectralInfinityNativeAmplitudeNonzero
public import ArtinMatthews.SpectralMixedCuspGap
public import ArtinMatthews.SpectralInfinityCuspAmplitude


set_option backward.privateInPublic true
@[expose] public section

/-! The actual trivial-character Gamma0 cusp spectrum has a uniform
3/16 lower bound. The level and mode are fixed before the small-scale limit. -/
noncomputable section
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0AllHeightGradientSpectralValue_ge_three_sixteenths (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    3/16 ≤ gamma0AllHeightGradientSpectralValue N i := by
  have h (M : ℕ) [NeZero M] (hM : M = 1*N) (j : Gamma0AllHeightSpectralIndex M) :
      3/16 ≤ gamma0AllHeightGradientSpectralValue M j := by
    subst M
    obtain ⟨n,hn,hAmp⟩ := gamma0InfinityNativeBesselAmplitude_exists_ne_zero (1*N) j 1 one_pos
    have hStep : gamma0CuspFrequencyStep (1*N) (1 : SL(2, ℤ)) = 1*N := by
      simpa only [gamma0CuspTrueWidth_identity, one_mul] using
        gamma0CuspFrequencyStep_mul_width (1*N) (1 : SL(2, ℤ))
    have hinfinity :
        gamma0CuspBesselAmplitude (1*N) j 1 1 one_pos
          ((gamma0CuspFrequencyStep (1*N) 1 : ℤ)*n)
          (gamma0CuspFrequencyStep_mul_ne_zero (1*N) 1 hn) ≠ 0 := by
      simpa only [hStep] using hAmp
    have hm (a : SL(2, ℤ)) (ha : a = gamma0CuspOneOver (1*N)) :
        gamma0CuspBesselAmplitude (1*N) j a 1 one_pos
          ((gamma0CuspFrequencyStep (1*N) a : ℤ)*n)
          (gamma0CuspFrequencyStep_mul_ne_zero (1*N) a hn) ≠ 0 := by
      subst a
      rw [gamma0CuspBesselAmplitude_oneOver_trueFrequency_eq_identity (1*N) j 1 one_pos n hn]
      exact hinfinity
    exact gamma0MixedCusp_spectralValue_ge_three_sixteenths_of_amplitude
      1 N (Nat.coprime_one_left N) j n hn (hm (gamma0CuspOneOver N) (by rw [one_mul]))
  exact h N (one_mul N).symm i

theorem gamma0AllHeightGradientSpectralGap_uniform :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N),
      δ ≤ gamma0AllHeightGradientSpectralValue N i :=
  ⟨3/16, by norm_num, gamma0AllHeightGradientSpectralValue_ge_three_sixteenths⟩

end ArtinMatthews
