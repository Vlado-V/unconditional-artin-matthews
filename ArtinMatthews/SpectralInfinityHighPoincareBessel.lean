module

public import ArtinMatthews.SpectralSameCuspPoincareGram


set_option backward.privateInPublic true
@[expose] public section

/-! Exact Gram and finite spectral Bessel bounds for infinity tests
above the geometric height threshold. The literal period-N factor
cancels on passing to actual unit-period Bessel amplitudes. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace BigOperators

namespace ArtinMatthews

theorem gamma0FourierPoincarePacket_identity_high_norm_sq {ι : Type*} (N : ℕ) [NeZero N]
    (t : Finset ι) (α : ι → ℂ) (ν : ι → ℤ) (hν : Function.Injective ν) (hν0 : ∀ j, ν j ≠ 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) {A : ℝ} (hA : 0 < A)
    (hρlo : ∀ y ∈ tsupport ρ, A ≤ y) (hcut : 1 < (N : ℝ)^2*A*A) :
    let nN j := (gamma0CuspFrequencyStep N 1 : ℤ)*ν j
    let P := gamma0FourierPoincarePacket N t α (fun _ => 1) nN (fun _ => ρ)
      (fun _ => hρ) (fun _ => hcρ) (fun _ => hpρ)
    ‖P‖^2 = 4*(N : ℝ)^2*cuspFourierHeightPairing ρ ρ*(∑ j ∈ t, ‖α j‖^2) := by
  dsimp only
  have hg := gamma0FourierPoincarePacket_sameCusp_gram N 1 t α ν hν ρ hρ hcρ hpρ
  dsimp only at hg
  have hz (j k : ι) := gamma0PositiveGeometricSum_identity_zero_of_high_support N (ν j) (ν k)
    (hν0 j) (hν0 k) ρ ρ hρ hρ hcρ hcρ hpρ hpρ hA hA hρlo hρlo hcut
  simp only [hz,mul_zero,Finset.sum_const_zero,add_zero] at hg
  simpa only [Complex.ofReal_re,gamma0CuspFrequencyStep_identity,pow_two,mul_assoc] using congrArg Complex.re hg

theorem gamma0FourierPoincarePacket_identity_high_finite_bessel {ι : Type*} (N : ℕ) [NeZero N]
    (u : Finset (Gamma0AllHeightSpectralIndex N)) (t : Finset ι)
    (α : ι → ℂ) (ν : ι → ℤ) (hν : Function.Injective ν) (hν0 : ∀ j, ν j ≠ 0)
    (Y : ℝ) (hY : 0 < Y) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y)
    {A : ℝ} (hA : 0 < A) (hρlo : ∀ y ∈ tsupport ρ, A ≤ y) (hcut : 1 < (N : ℝ)^2*A*A) :
    let nN j := (gamma0CuspFrequencyStep N 1 : ℤ)*ν j
    ∑ i ∈ u, ‖∑ j ∈ t, star (α j)*
      gamma0FourierPoincareSpectralCoefficient N i 1 Y hY (nN j)
        (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hν0 j)) ρ‖^2 ≤
      4*(N : ℝ)^2*cuspFourierHeightPairing ρ ρ*(∑ j ∈ t, ‖α j‖^2) := by
  dsimp only
  have h := gamma0FourierPoincarePacket_finite_bessel N u t α (fun _ => 1)
    (fun j => (gamma0CuspFrequencyStep N 1 : ℤ)*ν j)
    (fun j => gamma0CuspFrequencyStep_mul_ne_zero N 1 (hν0 j))
    Y hY (fun _ => ρ) (fun _ => hρ) (fun _ => hcρ) (fun _ => hpρ) (fun _ => hsρ)
  rwa [gamma0FourierPoincarePacket_identity_high_norm_sq N t α ν hν hν0 ρ hρ hcρ hpρ hA hρlo hcut] at h

theorem gamma0Infinity_high_bessel_amplitude_bound {ι : Type*} (N : ℕ) [NeZero N]
    (u : Finset (Gamma0AllHeightSpectralIndex N)) (t : Finset ι)
    (α : ι → ℂ) (ν : ι → ℤ) (hν : Function.Injective ν) (hν0 : ∀ j, ν j ≠ 0)
    (Y : ℝ) (hY : 0 < Y) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y)
    {A : ℝ} (hA : 0 < A) (hρlo : ∀ y ∈ tsupport ρ, A ≤ y) (hcut : 1 < (N : ℝ)^2*A*A) :
    let nN j := (gamma0CuspFrequencyStep N 1 : ℤ)*ν j
    ∑ i ∈ u, ‖∑ j ∈ t, star (α j)*
      gamma0CuspBesselAmplitude N i 1 Y hY (nN j) (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hν0 j))*
      cuspBesselTransform (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ)))
        |cuspFourierFrequency 1 (ν j)| Y ρ‖^2 ≤
      cuspFourierHeightPairing ρ ρ*(∑ j ∈ t, ‖α j‖^2) := by
  dsimp only
  let nN j := (gamma0CuspFrequencyStep N 1 : ℤ)*ν j
  let B (i : Gamma0AllHeightSpectralIndex N) (j : ι) := star (α j)*
      gamma0CuspBesselAmplitude N i 1 Y hY (nN j) (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hν0 j))*
      cuspBesselTransform (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ)))
        |cuspFourierFrequency 1 (ν j)| Y ρ
  have hf (j : ι) : |cuspFourierFrequency (N : ℝ) (nN j)| = |cuspFourierFrequency 1 (ν j)| := by
    simpa only [nN,gamma0CuspTrueWidth_identity,Nat.cast_one,mul_one] using
      cuspFourierFrequency_abs_trueWidth N 1 (ν j)
  have he (i : Gamma0AllHeightSpectralIndex N) :
      (∑ j ∈ t, star (α j)*gamma0FourierPoincareSpectralCoefficient N i 1 Y hY (nN j)
        (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hν0 j)) ρ) =
        (2*(N : ℂ))*(∑ j ∈ t, B i j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [gamma0FourierPoincareSpectralCoefficient,hf,B]
    ring
  have h := gamma0FourierPoincarePacket_identity_high_finite_bessel N u t α ν hν hν0
    Y hY ρ hρ hcρ hpρ hsρ hA hρlo hcut
  dsimp only at h
  simp only [nN] at he
  have hnorm (z : ℂ) : ‖(2*(N : ℂ))*z‖^2 = (2*(N : ℝ))^2*‖z‖^2 := by
    rw [norm_mul,norm_mul,Complex.norm_natCast,show ‖(2 : ℂ)‖ = (2 : ℝ) from Complex.norm_natCast 2]
    exact mul_pow _ _ _
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hscale : 0 < (2*(N : ℝ))^2 := by positivity
  change (∑ i ∈ u, ‖∑ j ∈ t, B i j‖^2) ≤ _
  apply (mul_le_mul_iff_of_pos_left hscale).mp
  calc
    _ ≤ 4*(N : ℝ)^2*cuspFourierHeightPairing ρ ρ*(∑ j ∈ t, ‖α j‖^2) := by
      rw [Finset.mul_sum]
      simpa only [he,hnorm] using h
    _ = _ := by ring

end ArtinMatthews
