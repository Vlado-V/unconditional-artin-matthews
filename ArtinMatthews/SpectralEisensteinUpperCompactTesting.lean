module

public import ArtinMatthews.SpectralCompactResolventMeromorphicTest


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine upper cutoff sufficiently far above the modular support
of a compact test leaves its literal pairing with Eisenstein unchanged. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem gamma0CuspUpperTruncatedProfile_eq_cutoff_on_support (N : ℕ) [NeZero N]
    (φ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N φ) (r : SL(2,ℤ))
    (q : ℂ) {A : ℝ} (hA : 0<A) (hcut : Y.height≤1/A)
    (z : UpperHalfPlane) (hz : z∈tsupport φ.val) :
    gamma0CuspHeightProfile N r (eisensteinOutgoingApprox q A) z=gamma0CuspEisensteinCutoff N r q z := by
  rw [gamma0CuspEisensteinCutoff_eq_profile]
  unfold gamma0CuspHeightProfile
  congr 1
  apply finsum_congr
  intro v
  let H := cuspEisensteinRowHeight N 1 r v z
  let w : ℝ := gamma0CuspTrueWidth N r
  have hw : 1≤w := by
    change (1:ℝ)≤(gamma0CuspTrueWidth N r:ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (gamma0CuspTrueWidth_pos N r).ne'
  have hH : H≤Y.height := Y.modular_height_le (gamma0CuspEisensteinRowRepresentative N 1 r v).val z hz
  have hHw : H/w≤H := div_le_self (cuspEisensteinRowHeight_pos N 1 r v z).le hw
  have hAh : A*(H/w)≤1 := by
    have he := (le_div_iff₀ hA).mp (hHw.trans (hH.trans hcut))
    simpa only [mul_comm A] using he
  change eisensteinOutgoingApprox q A (H/w)=eisensteinVerticalCutoffMode q (H/w)
  rw [eisensteinOutgoingApprox,eisensteinHeightCutoff_zero hAh,eisensteinVerticalCutoffMode]
  simp

theorem gamma0CuspUpperTruncatedEnergy_test_eq_cutoff (N : ℕ) [NeZero N]
    (φ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N φ)
    (r : SL(2,ℤ)) (q : ℂ) (A : ℝ) (hA : 0<A) (hcut : Y.height≤1/A) :
    inner ℂ (gamma0SmoothSeedMass N φ) (gamma0EnergyInclusion N (gamma0CuspUpperTruncatedEnergy N r q A hA))=
      (2:ℂ)*gamma0EisensteinCutoffCompactTest N r φ q := by
  let f := eisensteinOutgoingApprox q A
  let F := gamma0CuspHeightProfile N r f
  have hF : Continuous F := spectralSection_continuous _
    (gamma0CuspCompactHeightProfile_spatial_smooth N r f (eisensteinOutgoingApprox_smooth q A)
      (eisensteinOutgoingApprox_compact q hA) (eisensteinOutgoingApprox_positive_support q hA))
  have h := gamma0Mass_inner_unfold_representative N
    (gamma0EnergyInclusion N (gamma0CuspUpperTruncatedEnergy N r q A hA)) F hF
    (gamma0CuspHeightProfile_automorphy N r f)
    (gamma0CuspHeightProfileEnergy_mass_ae N r f (eisensteinOutgoingApprox_smooth q A)
      (eisensteinOutgoingApprox_compact q hA) (eisensteinOutgoingApprox_positive_support q hA)) φ
  rw [h,gamma0EisensteinCutoffCompactTest]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change inner ℂ (φ.val z) (F z)=inner ℂ (φ.val z) (gamma0CuspEisensteinCutoff N r q z)
    by_cases hz : φ.val z=0
    · rw [hz,inner_zero_left,inner_zero_left]
    · have he : F z=gamma0CuspEisensteinCutoff N r q z :=
        gamma0CuspUpperTruncatedProfile_eq_cutoff_on_support N φ Y r q hA hcut z (subset_tsupport φ.val hz)
      rw [he]

end ArtinMatthews
