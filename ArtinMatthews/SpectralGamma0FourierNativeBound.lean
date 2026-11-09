module

public import ArtinMatthews.SpectralGamma0FourierWindowBound


set_option backward.privateInPublic true
@[expose] public section

/-! Quantitative bounds for the actual completed Fourier coefficients, with height weight explicit. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0FullCuspidalFourierRepresentative_individual_bound
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y a b : ℝ) (hY : 0 < Y) (ha : Y < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Gamma0AllHeightSpectralIndex N) (n : ℤ) (y : ℝ), y ∈ Icc a b →
      ‖gamma0FullCuspidalFourierRepresentative N r Y hY i n y‖ ≤
        C*(1+gamma0AllHeightGradientSpectralValue N i) := by
  obtain ⟨C,hC,hb⟩ := gamma0FullCuspidalFourierRepresentative_spectral_frequency_window_bound N r Y a b hY ha
  refine ⟨C,hC,?_⟩
  intro i n y hy
  have h := hb (gamma0AllHeightGradientSpectralValue N i) {n} y hy
  simp only [Finset.sum_singleton] at h
  have hi : i ∈ gamma0AllHeightGradientSpectralCutoff N (gamma0AllHeightGradientSpectralValue N i) :=
    (mem_gamma0AllHeightGradientSpectralCutoff N _ i).mpr le_rfl
  have hterm := Finset.single_le_sum (s := gamma0AllHeightGradientSpectralCutoff N
      (gamma0AllHeightGradientSpectralValue N i))
    (f := fun j => ‖gamma0FullCuspidalFourierRepresentative N r Y hY j n y‖^2)
    (fun _ _ => sq_nonneg _) hi
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC.le
    (by linarith [gamma0AllHeightGradientSpectralValue_nonneg N i]))).mp (hterm.trans h)

theorem gamma0FullCuspidalFourier_native_window_bound_ae
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y a b : ℝ) (hY : 0 < Y) (ha : Y < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ y ∂volume.restrict (Icc a b),
      ∀ (R : ℝ) (t : Finset ℤ),
        (∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R, ∑ n ∈ t,
          ‖gamma0CuspFourierCoefficient N r Y hY n (gamma0FullCuspidalSpectralBasis N i).val y‖^2) ≤
            (C*(1+R))^2 := by
  obtain ⟨C,hC,hb⟩ := gamma0FullCuspidalFourierRepresentative_spectral_frequency_window_bound N r Y a b hY ha
  have hsub : Icc a b ⊆ Ioi Y := fun _ hy => ha.trans_le hy.1
  have he (i : Gamma0AllHeightSpectralIndex N) (n : ℤ) :=
    (gamma0FullCuspidalFourierRepresentative_native_ae N r Y hY i n).filter_mono
      (ae_mono (Measure.restrict_mono_set _ hsub))
  refine ⟨C,hC,?_⟩
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (he i)),ae_restrict_mem measurableSet_Icc]
    with y hy hyab
  intro R t
  have heq : (∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R, ∑ n ∈ t,
      ‖gamma0CuspFourierCoefficient N r Y hY n (gamma0FullCuspidalSpectralBasis N i).val y‖^2) =
      ∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R, ∑ n ∈ t,
        ‖gamma0FullCuspidalFourierRepresentative N r Y hY i n y‖^2 := by
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_congr rfl (fun n _ => congrArg (fun z : ℂ => ‖z‖^2) (hy i n))
  rw [heq]
  exact hb R t y hyab

theorem gamma0FullCuspidalFourier_native_weighted_window_bound_ae
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y a b : ℝ) (hY : 0 < Y) (ha : Y < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ y ∂volume.restrict (Icc a b),
      ∀ (R : ℝ) (t : Finset ℤ),
        (∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R, ∑ n ∈ t,
          ‖gamma0CuspFourierCoefficient N r Y hY n (gamma0FullCuspidalSpectralBasis N i).val y‖^2) / y^2 ≤
            (C*(1+R))^2 / y^2 := by
  obtain ⟨C,hC,hb⟩ := gamma0FullCuspidalFourier_native_window_bound_ae N r Y a b hY ha
  refine ⟨C,hC,hb.mono fun y hy R t => ?_⟩
  exact div_le_div_of_nonneg_right (hy R t) (sq_nonneg y)

theorem gamma0FullCuspidalFourier_twoCell_window_bound_ae
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y a b : ℝ) (hY : 0 < Y) (ha : Y < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ y ∂volume.restrict (Icc a b),
      ∀ (R : ℝ) (t : Finset ℤ),
        (∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R, ∑ n ∈ t,
          ‖gamma0CuspTwoCellFourierCoefficient N r Y hY n (gamma0FullCuspidalSpectralBasis N i).val y‖^2) ≤
            (C*(1+R))^2 := by
  obtain ⟨C,hC,hb⟩ := gamma0FullCuspidalFourierRepresentative_spectral_frequency_window_bound N r Y a b hY ha
  have hsub : Icc a b ⊆ Ioi Y := fun _ hy => ha.trans_le hy.1
  have he (i : Gamma0AllHeightSpectralIndex N) (n : ℤ) :=
    (gamma0FullCuspidalFourierRepresentative_twoCell_ae N r Y hY i n).filter_mono
      (ae_mono (Measure.restrict_mono_set _ hsub))
  refine ⟨C,hC,?_⟩
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (he i)),ae_restrict_mem measurableSet_Icc]
    with y hy hyab
  intro R t
  have heq : (∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R, ∑ n ∈ t,
      ‖gamma0CuspTwoCellFourierCoefficient N r Y hY n (gamma0FullCuspidalSpectralBasis N i).val y‖^2) =
      ∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R, ∑ n ∈ t,
        ‖gamma0FullCuspidalFourierRepresentative N r Y hY i n y‖^2 := by
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_congr rfl (fun n _ => congrArg (fun z : ℂ => ‖z‖^2) (hy i n))
  rw [heq]
  exact hb R t y hyab

end ArtinMatthews
