module

public import ArtinMatthews.SpectralInfinityHighProfileGram


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine common physical test for a packet of different cusp
frequencies, under the geometric high support condition. The resulting
spectral test factor depends on the spectral index alone. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein
open scoped MatrixGroups ContDiff InnerProductSpace BigOperators

namespace ArtinMatthews

theorem gamma0Infinity_common_physical_test_bessel {ι : Type*} (N : ℕ) [NeZero N]
    (u : Finset (Gamma0AllHeightSpectralIndex N)) (t : Finset ι)
    (α : ι → ℂ) (n : ι → ℤ) (hn : Function.Injective n) (hn0 : ∀ j, n j ≠ 0)
    (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    {A B Y : ℝ} (hA : 0 < A) (hB : 0 < B) (hY : 0 < Y) (hYB : Y < A/B)
    (hFB : tsupport F ⊆ Ici A) (hfreq : ∀ j, |cuspFourierFrequency 1 (n j)| ≤ B)
    (hcut : 1 < (N : ℝ)^2*(A/B)*(A/B)) :
    let nN j := (gamma0CuspFrequencyStep N 1 : ℤ)*n j
    let Fhat (i : Gamma0AllHeightSpectralIndex N) := ∫ x : ℝ, (F x : ℂ)*
      schlafliBesselK (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ))) x
      ∂spectralKLPhysicalMeasure
    (∑ i ∈ u, ‖Fhat i*(∑ j ∈ t, star (α j)*
      gamma0CuspBesselAmplitude N i 1 Y hY (nN j)
        (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hn0 j)))‖^2) ≤
      (∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure)*(∑ j ∈ t, ‖α j‖^2) := by
  dsimp only
  let nN j := (gamma0CuspFrequencyStep N 1 : ℤ)*n j
  let q j := |cuspFourierFrequency 1 (n j)|
  let ρ j := spectralFrequencyTestProfile (q j) F
  have hq (j : ι) : 0 < q j := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos (n j) (hn0 j))
  have hFp : tsupport F ⊆ Ioi (0 : ℝ) := fun _ hx => hA.trans_le (hFB hx)
  have hρ (j : ι) : ContDiff ℝ ∞ (ρ j) := spectralFrequencyTestProfile_contDiff (q j) F hF hFp
  have hcρ (j : ι) : HasCompactSupport (ρ j) := spectralFrequencyTestProfile_compact (q j) (hq j) F hcF
  have hlo (j : ι) (y : ℝ) (hy : y ∈ tsupport (ρ j)) : A/B ≤ y := by
    exact (div_le_div_of_nonneg_left hA.le (hq j) (hfreq j)).trans
      (spectralFrequencyTestProfile_support_lower (q j) (hq j) F hFB hy)
  have hpρ (j : ι) : tsupport (ρ j) ⊆ Ioi (0 : ℝ) :=
    fun y hy => (div_pos hA hB).trans_le (hlo j y hy)
  have hsρ (j : ι) : tsupport (ρ j) ⊆ Ioi Y := fun y hy => hYB.trans_le (hlo j y hy)
  let P := gamma0FourierPoincarePacket N t α (fun _ => 1) nN ρ hρ hcρ hpρ
  let M := ∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure
  let ν (i : Gamma0AllHeightSpectralIndex N) := Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ))
  let Fhat (i : Gamma0AllHeightSpectralIndex N) := ∫ x : ℝ, (F x : ℂ)*schlafliBesselK (ν i) x
    ∂spectralKLPhysicalMeasure
  let C (i : Gamma0AllHeightSpectralIndex N) (j : ι) :=
    gamma0CuspBesselAmplitude N i 1 Y hY (nN j) (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hn0 j))
  have hMass (j : ι) : cuspFourierHeightPairing (ρ j) (ρ j) = M :=
    spectralFrequencyTestProfile_height_mass (q j) (hq j) F
  have hP : ‖P‖^2 = (2*(N : ℝ))^2*M*(∑ j ∈ t, ‖α j‖^2) := by
    have h := gamma0FourierPoincarePacket_identity_high_profile_normsq N t α n hn hn0
      ρ hρ hcρ hpρ (div_pos hA hB) hlo hcut
    change ‖P‖^2 = _ at h
    simp only [hMass,← Finset.sum_mul] at h
    rw [h]
    ring
  have hqN (j : ι) : |cuspFourierFrequency (N : ℝ) (nN j)| = q j := by
    simpa only [nN,q,gamma0CuspTrueWidth_identity,Nat.cast_one,mul_one] using
      cuspFourierFrequency_abs_trueWidth N 1 (n j)
  have hCoeff (i : Gamma0AllHeightSpectralIndex N) (j : ι) :
      gamma0FourierPoincareSpectralCoefficient N i 1 Y hY (nN j)
        (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hn0 j)) (ρ j) =
        (2*(N : ℂ))*C i j*Fhat i := by
    rw [gamma0FourierPoincareSpectralCoefficient,hqN,
      spectralFrequencyTestProfile_transform (q j) (hq j) F (ν i) Y hY.le (hsρ j)]
  have hrow (i : Gamma0AllHeightSpectralIndex N) :
      (∑ j ∈ t, star (α j)*gamma0FourierPoincareSpectralCoefficient N i 1 Y hY (nN j)
        (gamma0CuspFrequencyStep_mul_ne_zero N 1 (hn0 j)) (ρ j)) =
        (2*(N : ℂ))*(Fhat i*(∑ j ∈ t, star (α j)*C i j)) := by
    simp only [hCoeff,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hnorm (z : ℂ) : ‖(2*(N : ℂ))*z‖^2 = (2*(N : ℝ))^2*‖z‖^2 := by
    rw [norm_mul,norm_mul,Complex.norm_natCast,show ‖(2 : ℂ)‖ = (2 : ℝ) from Complex.norm_natCast 2]
    exact mul_pow _ _ _
  have hBessel := gamma0FourierPoincarePacket_finite_bessel N u t α (fun _ => 1) nN
    (fun j => gamma0CuspFrequencyStep_mul_ne_zero N 1 (hn0 j)) Y hY
    ρ hρ hcρ hpρ hsρ
  simp only [hrow,hnorm] at hBessel
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  change (∑ i ∈ u, ‖Fhat i*(∑ j ∈ t, star (α j)*C i j)‖^2) ≤ M*(∑ j ∈ t, ‖α j‖^2)
  apply (mul_le_mul_iff_of_pos_left (show 0 < (2*(N : ℝ))^2 by positivity)).mp
  calc
    _ ≤ ‖P‖^2 := by rw [Finset.mul_sum]; exact hBessel
    _ = _ := by rw [hP,mul_assoc]

end ArtinMatthews
