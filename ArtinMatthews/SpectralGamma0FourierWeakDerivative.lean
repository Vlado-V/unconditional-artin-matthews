module

public import ArtinMatthews.SpectralGamma0FourierEnergy
public import ArtinMatthews.SpectralCuspConstantTermWeakDerivative


set_option backward.privateInPublic true
@[expose] public section

/-! The actual completed Fourier coefficient has the projection of the
completed physical vertical derivative as its weak derivative. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem cuspHorizontalWeightedMean_weak_verticalDerivative (w : ℝ)
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
    (∫ y, deriv ρ y • cuspHorizontalWeightedMean w χ F y) =
      -(∫ y, ρ y • cuspHorizontalWeightedMean w χ (fun p => fderiv ℝ F p (0, 1)) y) := by
  have hG : ContDiff ℝ ∞ (fun p : ℝ × ℝ => χ p.1 * F p) :=
    (hχ.comp contDiff_fst).mul hF
  have he : (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => χ q.1 * F q) p (0, 1)) =
      (fun p => χ p.1 * fderiv ℝ F p (0, 1)) :=
    funext (spectralPlane_vertical_product χ F hχ hF)
  simpa only [cuspHorizontalWeightedMean, he] using
    cuspHorizontalMean_weak_verticalDerivative hG w ρ hρ hρc

theorem gamma0CuspFourier_weak_scaledDerivative (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρs : tsupport ρ ⊆ Ioi Y) (u : gamma0EnergySpace N) :
    (∫ y in Ioi Y, deriv ρ y • gamma0CuspFourierCoefficient N r Y hY n
        (gamma0EnergyInclusion N u) y) =
      -(∫ y in Ioi Y, (ρ y / y) • gamma0CuspFourierScaledDerivative N r Y hY n u y) := by
  have hw : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hρpos : tsupport ρ ⊆ Ioi (0 : ℝ) := fun _ hy => hY.trans (hρs hy)
  have hκ : Continuous (fun y => ρ y / y) := by
    simpa only [pow_one] using (spectralPositiveTest_div_pow_contDiff ρ hρ hρpos 1).continuous
  have hκc : HasCompactSupport (fun y => ρ y / y) := by
    simpa only [pow_one] using spectralPositiveTest_div_pow_compact ρ hρc 1
  let T := cuspVerticalCompactTest hw hY (deriv ρ) (hρ.continuous_deriv (by simp)) hρc.deriv
  let S := cuspVerticalCompactTest hw hY (fun y => ρ y / y) hκ hκc
  have he : T (gamma0CuspFourierCoefficient N r Y hY n (gamma0EnergyInclusion N u)) =
      -S (gamma0CuspFourierScaledDerivative N r Y hY n u) := by
    apply isClosed_property (gamma0EnergyTest_dense N)
      (isClosed_eq (T.continuous.comp ((gamma0CuspFourierCoefficient N r Y hY n).continuous.comp
        (gamma0EnergyInclusion N).continuous))
        (continuous_neg.comp (S.continuous.comp (gamma0CuspFourierScaledDerivative N r Y hY n).continuous)))
    intro ψ
    change T (gamma0CuspFourierCoefficient N r Y hY n
      (gamma0EnergyInclusion N (gamma0EnergyTest N ψ))) =
        -S (gamma0CuspFourierScaledDerivative N r Y hY n (gamma0EnergyTest N ψ))
    rw [gamma0EnergyInclusion_test]
    change cuspVerticalCompactTest hw hY (deriv ρ) _ _ _ =
      -cuspVerticalCompactTest hw hY (fun y => ρ y / y) hκ hκc _
    rw [cuspVerticalCompactTest_apply, cuspVerticalCompactTest_apply]
    let F := gamma0CuspSeedPlaneExtension N ψ r Y
    have hF : ContDiff ℝ ∞ F :=
      spectralSectionSmoothExtension_contDiff hY _ (gamma0CuspSection_smooth N ψ r)
    have hc := (spectralHorizontal_cuspVertical_ae_iff hY).mp
      (gamma0CuspFourierCoefficient_seed_ae N ψ r Y hY n)
    have hd := (spectralHorizontal_cuspVertical_ae_iff hY).mp
      (gamma0CuspFourierDerivative_seed_ae N ψ r Y hY n)
    have hleft : (∫ y in Ioi Y, deriv ρ y • gamma0CuspFourierCoefficient N r Y hY n
        (gamma0SmoothSeedMass N ψ) y) =
        ∫ y in Ioi Y, deriv ρ y • cuspHorizontalWeightedMean (N : ℝ)
          (cuspFourierPhase (N : ℝ) n) F y := by
      apply integral_congr_ae
      exact hc.mono fun y hy => by dsimp only; rw [hy]
    have hright : (∫ y in Ioi Y, (ρ y / y) • gamma0CuspFourierScaledDerivative N r Y hY n
        (gamma0EnergyTest N ψ) y) =
        ∫ y in Ioi Y, ρ y • cuspHorizontalWeightedMean (N : ℝ)
          (cuspFourierPhase (N : ℝ) n) (fun p => fderiv ℝ F p (0, 1)) y := by
      apply integral_congr_ae
      filter_upwards [hd] with y hy
      rw [div_eq_mul_inv, mul_smul]
      change ρ y • gamma0CuspFourierDerivative N r Y hY n (gamma0EnergyTest N ψ) y = _
      rw [hy]
    rw [hleft, hright,
      spectralTest_setIntegral_eq_integral (deriv ρ) (Ioi Y) (tsupport_deriv_subset.trans hρs),
      spectralTest_setIntegral_eq_integral ρ (Ioi Y) hρs]
    exact cuspHorizontalWeightedMean_weak_verticalDerivative (N : ℝ)
      (cuspFourierPhase (N : ℝ) n) (cuspFourierPhase_contDiff (N : ℝ) n) F hF ρ hρ hρc
  simpa only [T, S, cuspVerticalCompactTest_apply] using he

theorem gamma0CuspFourier_weak_derivative (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρs : tsupport ρ ⊆ Ioi Y) (u : gamma0EnergySpace N) :
    (∫ y in Ioi Y, deriv ρ y • gamma0CuspFourierCoefficient N r Y hY n
        (gamma0EnergyInclusion N u) y) =
      -(∫ y in Ioi Y, ρ y • gamma0CuspFourierDerivative N r Y hY n u y) := by
  have he := gamma0CuspFourier_weak_scaledDerivative N r Y hY n ρ hρ hρc hρs u
  simpa only [gamma0CuspFourierDerivative, div_eq_mul_inv, mul_smul] using he

end ArtinMatthews
