module

public import ArtinMatthews.SpectralGamma0FourierNativeBound


set_option backward.privateInPublic true
@[expose] public section

/-! Integrated joint spectral/Fourier windows for actual completed cusp coefficients.
The explicit height loss is a⁻² on the fixed positive band [a,b]. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0FullCuspidalFourier_native_band_integrable
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y a b : ℝ) (hY : 0 < Y) (ha : Y < a)
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (t : Finset ℤ) :
    IntegrableOn (fun y =>
      (∑ i ∈ s, ∑ n ∈ t,
        ‖gamma0CuspFourierCoefficient N r Y hY n (gamma0FullCuspidalSpectralBasis N i).val y‖^2) / y^2)
      (Icc a b) := by
  have hi (i : Gamma0AllHeightSpectralIndex N) (n : ℤ) :
      IntegrableOn (fun y =>
        ‖gamma0CuspFourierCoefficient N r Y hY n (gamma0FullCuspidalSpectralBasis N i).val y‖^2 / y^2)
        (Icc a b) :=
    (gamma0CuspFourierCoefficient_integrable_mass N r Y hY n _).mono_set
      (fun _ hy => ha.trans_le hy.1)
  change Integrable _ (volume.restrict (Icc a b))
  convert (integrable_finsetSum s (fun i _ => integrable_finsetSum t (fun n _ => hi i n))) using 1
  funext y
  simp only [Finset.sum_div]

theorem gamma0FullCuspidalFourier_native_band_bound
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y a b : ℝ) (hY : 0 < Y) (ha : Y < a)
    (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (t : Finset ℤ),
      (∫ y in a..b,
        (∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R, ∑ n ∈ t,
          ‖gamma0CuspFourierCoefficient N r Y hY n (gamma0FullCuspidalSpectralBasis N i).val y‖^2) / y^2)
      ≤ (b-a) * (C*(1+R))^2 / a^2 := by
  obtain ⟨C,hC,hb⟩ := gamma0FullCuspidalFourier_native_window_bound_ae N r Y a b hY ha
  refine ⟨C,hC,?_⟩
  intro R t
  have ha0 : 0 < a := hY.trans ha
  have hf : IntervalIntegrable (fun y =>
      (∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R, ∑ n ∈ t,
        ‖gamma0CuspFourierCoefficient N r Y hY n (gamma0FullCuspidalSpectralBasis N i).val y‖^2) / y^2)
      volume a b := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using
      gamma0FullCuspidalFourier_native_band_integrable N r Y a b hY ha
        (gamma0AllHeightGradientSpectralCutoff N R) t
  have hg : IntervalIntegrable (fun _ : ℝ => (C*(1+R))^2/a^2) volume a b :=
    intervalIntegrable_const
  have hm : (fun y =>
      (∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R, ∑ n ∈ t,
        ‖gamma0CuspFourierCoefficient N r Y hY n (gamma0FullCuspidalSpectralBasis N i).val y‖^2) / y^2)
      ≤ᵐ[volume.restrict (Icc a b)] (fun _ => (C*(1+R))^2/a^2) := by
    filter_upwards [hb,ae_restrict_mem measurableSet_Icc] with y hy hyab
    exact (div_le_div_of_nonneg_right (hy R t) (sq_nonneg y)).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos ha0)
        (pow_le_pow_left₀ ha0.le hyab.1 2))
  calc
    _ ≤ ∫ _y in a..b, (C*(1+R))^2/a^2 :=
      intervalIntegral.integral_mono_ae_restrict hab hf hg hm
    _ = (b-a) * (C*(1+R))^2 / a^2 := by
      rw [intervalIntegral.integral_const,smul_eq_mul]
      ring

end ArtinMatthews
