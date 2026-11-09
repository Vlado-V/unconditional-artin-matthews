module

public import ArtinMatthews.SpectralEisensteinFourierCompact
public import ArtinMatthews.SpectralCuspUnitFourierRegularity
public import ArtinMatthews.SpectralCuspFourierWeakIdentification


set_option backward.privateInPublic true
@[expose] public section

/-! The completed continued Fourier coefficient agrees almost everywhere
with the literal unit-period coefficient of the convergent Eisenstein series
on Re(s)>1. Identification uses actual compact tests. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

theorem gamma0CuspEisensteinMeromorphicTest_fourier_initial (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m : ℤ) (s : ℂ) (hs : 1 < s.re)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y) :
    let mN := (gamma0CuspFrequencyStep N r : ℤ)*m
    let ψ := modularTranslateSmoothSeed r
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) mN ρ hρ hcρ hpρ)
    gamma0CuspEisensteinMeromorphicTest N a ψ s =
      (2*(N : ℝ)) • ∫ y in Ioi Y, (ρ y/y^2) •
        gamma0UnitCuspFourierMean N r m (gamma0CuspEisenstein N a s)
          (y/(gamma0CuspTrueWidth N r : ℝ)) := by
  dsimp only
  rw [gamma0CuspEisensteinMeromorphicTest_initial N a _ s hs,
    h2_compactSeed_inner_modularTranslate,
    (gamma0Invariant_unit_fourier_test N r (gamma0CuspEisenstein N a s)
      (gamma0CuspEisenstein_continuous N a s hs) (gamma0CuspEisenstein_automorphy N a s)
      Y hY m ρ hρ hcρ hpρ hsρ).2]
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat]
  ring

theorem gamma0CuspEisensteinFourierCoefficient_locallyIntegrable (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m : ℤ) (s : ℂ) :
    LocallyIntegrableOn (gamma0CuspEisensteinFourierCoefficient N a r Y hY m s) (Ioi Y) := by
  have hC (b : SL(2, ℤ)) (z : ℂ) : ContinuousOn
      (fun y => gamma0UnitCuspFourierMean N r m (gamma0CuspEisensteinCutoff N b z)
        (y/(gamma0CuspTrueWidth N r : ℝ))) (Ioi Y) :=
    (gamma0UnitCuspFourierMean_raw_continuousOn N r m _
      (gamma0CuspOutgoingCutoff_continuous N b z)).mono (fun _ hy => hY.trans hy)
  have hSum : ContinuousOn (fun y => ∑ j : Gamma0EisensteinCuspClasses N,
      gamma0EisensteinMatchedCoefficient N a s j *
        gamma0UnitCuspFourierMean N r m
          (gamma0CuspEisensteinCutoff N (gamma0EisensteinCuspClassRepresentative N j) (1-s))
          (y/(gamma0CuspTrueWidth N r : ℝ))) (Ioi Y) :=
    continuousOn_finsetSum _ (fun _ _ => continuousOn_const.mul (hC _ _))
  exact ((hC a s).locallyIntegrableOn measurableSet_Ioi |>.add
    (cuspVerticalL2_locallyIntegrableOn (N : ℝ) Y (Nat.cast_pos.mpr (NeZero.pos N)) hY
      (gamma0CuspFourierCoefficient N r Y hY ((gamma0CuspFrequencyStep N r : ℤ)*m)
        (gamma0EnergyInclusion N (gamma0CuspEisensteinMatchedTruncatedEnergy N a s))))) |>.add
    (hSum.locallyIntegrableOn measurableSet_Ioi)

theorem gamma0CuspEisensteinFourierCoefficient_initial_ae (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m : ℤ) (s : ℂ) (hs : 1 < s.re) :
    gamma0CuspEisensteinFourierCoefficient N a r Y hY m s =ᵐ[volume.restrict (Ioi Y)]
      fun y => gamma0UnitCuspFourierMean N r m (gamma0CuspEisenstein N a s)
        (y/(gamma0CuspTrueWidth N r : ℝ)) := by
  let C := gamma0CuspEisensteinFourierCoefficient N a r Y hY m s
  let V (y : ℝ) := gamma0UnitCuspFourierMean N r m (gamma0CuspEisenstein N a s)
    (y/(gamma0CuspTrueWidth N r : ℝ))
  have hCl : LocallyIntegrableOn C (Ioi Y) :=
    gamma0CuspEisensteinFourierCoefficient_locallyIntegrable N a r Y hY m s
  have hVc : ContinuousOn V (Ioi Y) :=
    (gamma0UnitCuspFourierMean_raw_continuousOn N r m _
      (gamma0CuspEisenstein_continuous N a s hs)).mono (fun _ hy => hY.trans hy)
  have hVl : LocallyIntegrableOn V (Ioi Y) := hVc.locallyIntegrableOn measurableSet_Ioi
  have htest (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
      (hsρ : tsupport ρ ⊆ Ioi Y) : (∫ y,ρ y • (C y-V y)) = 0 := by
    let σ (y : ℝ) := ρ y*y^2
    have hσ : ContDiff ℝ ∞ σ := hρ.mul (contDiff_id.pow 2)
    have hcσ : HasCompactSupport σ := hcρ.mul_right
    have hsσ : tsupport σ ⊆ Ioi Y := tsupport_mul_subset_left.trans hsρ
    have hpσ : tsupport σ ⊆ Ioi (0 : ℝ) := fun y hy => hY.trans (hsσ hy)
    have hPair := (gamma0CuspEisensteinMeromorphicTest_fourier N a r Y hY m s
      σ hσ hcσ hpσ hsσ).symm.trans
      (gamma0CuspEisensteinMeromorphicTest_fourier_initial N a r Y hY m s hs σ hσ hcσ hpσ hsσ)
    have hEq : (∫ y in Ioi Y,(σ y/y^2) • C y) = ∫ y in Ioi Y,(σ y/y^2) • V y :=
      (smul_right_injective ℂ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
        (by exact_mod_cast NeZero.ne N))) hPair
    have hCancel (y : ℝ) (hy : y ∈ Ioi Y) : σ y/y^2 = ρ y := by
      dsimp only [σ]
      exact mul_div_cancel_right₀ _ (pow_ne_zero 2 (hY.trans hy).ne')
    have hCEq : (∫ y in Ioi Y,(σ y/y^2) • C y) = ∫ y in Ioi Y,ρ y • C y :=
      integral_congr_ae (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy; rw [hCancel y hy])
    have hVEq : (∫ y in Ioi Y,(σ y/y^2) • V y) = ∫ y in Ioi Y,ρ y • V y :=
      integral_congr_ae (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy; rw [hCancel y hy])
    rw [hCEq,hVEq,spectralTest_setIntegral_eq_integral ρ (Ioi Y) hsρ,
      spectralTest_setIntegral_eq_integral ρ (Ioi Y) hsρ] at hEq
    simp_rw [smul_sub]
    rw [integral_sub (spectral_integrable_local_test hCl hρ.continuous hcρ hsρ)
      (spectral_integrable_local_test hVl hρ.continuous hcρ hsρ),hEq,sub_self]
  have hz := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hCl.sub hVl) htest
  filter_upwards [ae_restrict_of_ae hz,ae_restrict_mem measurableSet_Ioi] with y hy hyS
  exact sub_eq_zero.mp (hy hyS)

end ArtinMatthews

