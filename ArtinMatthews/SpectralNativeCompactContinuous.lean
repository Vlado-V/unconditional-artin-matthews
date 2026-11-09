module

public import ArtinMatthews.SpectralNativeOrderTransform
public import ArtinMatthews.SpectralPrimitiveFourierCritical
public import ArtinMatthews.SpectralEisensteinTestCalibration


set_option backward.privateInPublic true
@[expose] public section

/-! Compact native Eisenstein analysis equals the genuine arithmetic
amplitude times the physical K integral. Its auxiliary height is arbitrary. -/

noncomputable section
open Set MeasureTheory Filter OAI.CubicEisenstein
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0PrimitiveAnalysis_fourier_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (Z : ℝ) (hZ : 0 < Z)
    (Y : ℝ) (hY : 0 < Y) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) (i : Gamma0EisensteinCuspClasses N) :
    (gamma0EisensteinAnalysis N (gamma0PrimitiveFourierPoincareTest N r n ρ hρ hcρ hpρ)) i
      =ᵐ[gamma0EisensteinSpectralMeasure] fun t => star
        (gamma0PrimitiveFourierAmplitude N (gamma0EisensteinCuspClassRepresentative N i) r Z hZ n hn
          (eisensteinCriticalPoint t)*
          ∫ x in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) x*
            (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 n|
              (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y)) x/(x : ℂ))) := by
  let a := gamma0EisensteinCuspClassRepresentative N i
  let ψ := gamma0PrimitiveFourierPoincareSeed N r n ρ hρ hcρ hpρ
  have hac : gamma0EisensteinSpectralMeasure ≪ (volume : Measure ℝ) := by
    exact Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict
  have hfactor := hac.ae_eq (gamma0PrimitiveFourierAmplitude_factorization_critical_ae N a r Y hY n hn
    ρ hρ hcρ hsρ)
  have hheight := hac.ae_eq (gamma0PrimitiveFourierAmplitude_height_critical_ae N a r Y Z hY hZ n hn)
  have hw : 0 < (gamma0CuspTrueWidth N r : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hq : 0 < |cuspFourierFrequency 1 n| := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hfreq : |cuspFourierFrequency 1 n| = 2*Real.pi*|(n : ℝ)| := by
    unfold cuspFourierFrequency
    rw [div_one,abs_mul,abs_of_pos (mul_pos two_pos Real.pi_pos)]
  have hs := (spectral_cusp_width_test_properties _ Y hw ρ hρ.continuous hcρ hsρ).2.2
  change (gamma0EisensteinAnalysis N (gamma0SmoothSeedMass N ψ)) i =ᵐ[gamma0EisensteinSpectralMeasure] _
  rw [gamma0EisensteinAnalysis_seed,gamma0EisensteinSeedAnalysis_apply]
  filter_upwards [gamma0EisensteinCoefficientLp_ae N i ψ,hfactor,hheight] with t ht hf hh
  rw [ht]
  change star (gamma0CuspEisensteinMeromorphicTest N a ψ (eisensteinCriticalPoint t)) = _
  rw [← gamma0PrimitiveEisensteinTransform_eq_test N a r Y hY n (eisensteinCriticalPoint t)
    ρ hρ hcρ hpρ hsρ,hf,hh,gamma0PrimitiveKTransform_critical,← hfreq,
    cuspBesselTransform_eq_order_integral _ hq (div_pos hY hw) _ hs]

end ArtinMatthews
