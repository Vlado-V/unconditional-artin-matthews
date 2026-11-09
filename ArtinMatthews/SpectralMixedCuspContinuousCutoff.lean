module

public import ArtinMatthews.SpectralMixedCuspContinuousDyadic
public import ArtinMatthews.SpectralFiniteDyadicIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! The actual positive-frequency Eisenstein density at 1/s satisfies
the level-uniform source cutoff bound in its native measure. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0MixedCusp_continuous_cutoff_orbit_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (r s : ℕ) [NeZero r] [NeZero s], r.Coprime s →
      ∀ (n : ℤ) (hn : n ≠ 0) {R Y : ℝ}, 1 ≤ R → ∀ hY : 0 < Y,
      Y < (1/16)/(|cuspFourierFrequency 1 n| /
        (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)) →
      let f := gamma0ContinuousPrincipalDensity (r*s) (gamma0CuspOneOver s) Y hY n hn
      let U := (fun t : ℝ => 1+|t|) ⁻¹' Icc 1 R
      IntegrableOn f U gamma0EisensteinSpectralMeasure ∧
        (∫ t in U, f t ∂gamma0EisensteinSpectralMeasure) ≤
          C*(R^2+|cuspFourierFrequency 1 n| * R/((r*s : ℕ) : ℝ)) := by
  obtain ⟨C,hC,hDyad⟩ := gamma0MixedCusp_continuous_dyadic_orbit_bound
  refine ⟨2*C,by positivity,?_⟩
  intro r s ir is hcop n hn R Y hR hY hYA
  let N := r*s
  let b := gamma0CuspOneOver s
  let q := |cuspFourierFrequency 1 n|
  let w := (gamma0CuspTrueWidth N b : ℝ)
  let μ := gamma0EisensteinSpectralMeasure
  let f := gamma0ContinuousPrincipalDensity N b Y hY n hn
  let τ (t : ℝ) := 1+|t|
  have hp : 0 < q/w := div_pos (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn))
    (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N b))
  have hτ : Measurable τ := by unfold τ; fun_prop
  have hf (t : ℝ) : 0 ≤ f t := div_nonneg
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Real.cosh_pos _).le
  have hWin (k : ℕ) :
      IntegrableOn f (τ ⁻¹' Icc ((2 : ℝ)^k) (2*(2 : ℝ)^k)) μ ∧
        (∫ t in τ ⁻¹' Icc ((2 : ℝ)^k) (2*(2 : ℝ)^k), f t ∂μ) ≤
          C*(((2 : ℝ)^k)^2+(q/(N : ℝ))*(2 : ℝ)^k) := by
    let T : ℝ := 2^k
    have hT : 1 ≤ T := one_le_pow₀ (by norm_num)
    have hY' : Y < (T/16)/(q/w) := hYA.trans_le
      (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hT (by norm_num)) hp.le)
    have h := hDyad r s hcop n hn (T := T) (Y := Y) (by linarith only [hT]) hY hY'
    change IntegrableOn f (spectralPrincipalBand T) μ ∧
      (∫ t in spectralPrincipalBand T, f t ∂μ) ≤ C*(T^2+q*T/(N : ℝ)) at h
    simpa only [spectralPrincipalBand,τ,T,show (q/(N : ℝ))*(2 : ℝ)^k = q*(2 : ℝ)^k/(N : ℝ) by ring]
      using h
  have h := spectral_nonneg_dyadic_cutoff_integral_le μ τ f hτ hf hR
    (B := q/(N : ℝ)) (by dsimp only [q]; positivity) hC.le hWin
  simpa only [show (q/(N : ℝ))*R = q*R/(N : ℝ) by ring] using h

end ArtinMatthews
