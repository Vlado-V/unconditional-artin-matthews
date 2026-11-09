module

public import ArtinMatthews.SpectralStoneAllEnergyAtoms
public import ArtinMatthews.SpectralCuspFourierTestPairing
public import ArtinMatthews.SpectralCompactResolventCuspSupport


set_option backward.privateInPublic true
@[expose] public section

/-! One compact zero-mode seed has the same valid height cutoff after
every modular translation. The zero Fourier projection is the actual
completed constant term. -/
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem cuspFourierMultiplier_zero (w Y T : ℝ) (f : CuspStripL2 w Y) :
    cuspFourierMultiplier w Y T 0 f=f := by
  apply Lp.ext
  have h := cuspFourierMultiplyLp_ae w Y T 0 f
  filter_upwards [h] with p hp
  change (cuspFourierMultiplyLp w Y T 0 f) p=f p
  simpa only [cuspFourierPhase,cuspFourierFrequency,Int.cast_zero,mul_zero,zero_mul,zero_div,neg_zero,
    Complex.ofReal_zero,Complex.exp_zero,one_mul] using hp

theorem gamma0CuspFourierCoefficient_zero (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0<Y) (f : Gamma0RegionL2 N) :
    gamma0CuspFourierCoefficient N r Y hY 0 f=gamma0CuspConstantTerm N r Y hY f := by
  change (cuspVerticalPullback (N:ℝ) Y).toContinuousLinearMap.adjoint
      (cuspFourierMultiplier (N:ℝ) Y (N:ℝ) 0
        ((cuspHyperbolicPullback (N:ℝ) Y hY).toContinuousLinearMap.adjoint
          (gamma0CuspMassRestriction N r Y hY f)))=_
  rw [cuspFourierMultiplier_zero]
  rfl

def Gamma0CompactResolventCutoff.modularTranslate {N : ℕ} [NeZero N] {ψ : h2SmoothCompactSeeds}
    (A : Gamma0CompactResolventCutoff N ψ) (r : SL(2,ℤ)) :
    Gamma0CompactResolventCutoff N (modularTranslateSmoothSeed r ψ) where
  height := A.height
  matching_le := A.matching_le
  modular_height_le δ z hz := by
    have hZ : r • z∈tsupport ψ.val := by
      change z∈tsupport (ψ.val ∘ Homeomorph.smul (Matrix.SpecialLinearGroup.mapGL ℝ r)) at hz
      rw [tsupport_comp_eq_preimage] at hz
      exact hz
    have h := A.modular_height_le (δ*r⁻¹) (r • z) hZ
    simpa only [mul_smul,inv_smul_smul] using h

theorem gamma0StoneGoodEnergy_modularTranslate (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ) (r : SL(2,ℤ)) :
    gamma0StoneGoodEnergy N (modularTranslateSmoothSeed r ψ) (A.modularTranslate r)=
      gamma0StoneGoodEnergy N ψ A := rfl

theorem gamma0ZeroModeProbe_pairing (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    (Y : ℝ) (hY : 0<Y) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ⊆Ioi (0:ℝ)) (hsρ : tsupport ρ⊆Ioi Y) (f : Gamma0RegionL2 N) :
    inner ℂ (gamma0FourierPoincareTest N r 0 ρ hρ hcρ hpρ) f=
      (2*(N:ℂ))*(∫ y in Ioi Y,(ρ y/y^2) • gamma0GlobalCuspConstantTerm N r f y) := by
  rw [gamma0FourierPoincareTest_inner N r Y hY 0 ρ hρ hcρ hpρ hsρ f,
    gamma0CuspFourierCoefficient_zero,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat]
  congr 1
  apply integral_congr_ae
  have h : gamma0GlobalCuspConstantTerm N r f =ᵐ[volume.restrict (Ioi Y)]
      (fun y => gamma0CuspConstantTerm N r Y hY f y) :=
    (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hY).mp
      (gamma0GlobalCuspConstantTerm_ae N r f Y hY)
  exact h.symm.mono (fun y hy => congrArg (fun z : ℂ => (ρ y/y^2) • z) hy)

end ArtinMatthews
