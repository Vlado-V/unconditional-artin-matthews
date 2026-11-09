module

public import ArtinMatthews.SpectralGamma0FourierRepresentative


set_option backward.privateInPublic true
@[expose] public section

/-! Joint spectral/frequency Bessel bounds on compact horocycle bands.
The coefficients retain the literal phase period N and horizontal normalization 1/N. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0FullCuspidalFourierRepresentative_weighted_window_bound
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y a b : ℝ) (hY : 0 < Y) (ha : Y < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Gamma0AllHeightSpectralIndex N)) (t : Finset ℤ)
      (y : ℝ), y ∈ Icc a b →
      (∑ i ∈ s, i.1.re^2*(∑ n ∈ t,
        ‖gamma0FullCuspidalFourierRepresentative N r Y hY i n y‖^2)) ≤ C^2 := by
  have hN : 0 < (N:ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  let K := Icc ((N:ℝ)/2) (3*(N:ℝ)/2) ×ˢ Icc a b
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKΩ : K ⊆ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2} := by
    intro p hp
    exact ⟨by linarith [hp.1.1],by linarith [hp.1.2],ha.trans_le hp.2.1⟩
  obtain ⟨C,hC,hb⟩ := gamma0FullCuspidalPlaneRepresentative_green_weighted_sum_bound N r Y hY hK hKΩ
  refine ⟨C,hC,?_⟩
  intro s t y hy
  have hYy : Y < y := ha.trans_le hy.1
  let F := fun i : Gamma0AllHeightSpectralIndex N => gamma0FullCuspidalPlaneRepresentative N r Y hY i
  have hI (i : Gamma0AllHeightSpectralIndex N) :
      IntegrableOn (fun x : ℝ => ‖F i (x+(N:ℝ)/2,y)‖^2) (Ioc 0 (N:ℝ)) :=
    (cuspInterior_shift_slice_memLp (N:ℝ) Y hN (F i)
      (gamma0FullCuspidalPlaneRepresentative_spec N r Y hY i).1 y hYy).integrable_norm_pow (by norm_num)
  have hIw (i : Gamma0AllHeightSpectralIndex N) :
      IntegrableOn (fun x : ℝ => i.1.re^2*‖F i (x+(N:ℝ)/2,y)‖^2) (Ioc 0 (N:ℝ)) :=
    (hI i).const_mul _
  have hSum : IntegrableOn (fun x : ℝ => ∑ i ∈ s, i.1.re^2*‖F i (x+(N:ℝ)/2,y)‖^2)
      (Ioc 0 (N:ℝ)) := integrable_finsetSum s (fun i _ => hIw i)
  have hConst : IntegrableOn (fun _ : ℝ => C^2) (Ioc 0 (N:ℝ)) :=
    continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hint : (∫ x in Ioc 0 (N:ℝ), ∑ i ∈ s, i.1.re^2*‖F i (x+(N:ℝ)/2,y)‖^2) ≤
      ∫ _x in Ioc 0 (N:ℝ), C^2 := by
    apply integral_mono_ae hSum hConst
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hb s (x+(N:ℝ)/2,y) ⟨⟨by linarith [hx.1],by linarith [hx.2]⟩,hy⟩
  calc
    _ ≤ ∑ i ∈ s, i.1.re^2*((N:ℝ)⁻¹*(∫ x in (0:ℝ)..(N:ℝ), ‖F i (x+(N:ℝ)/2,y)‖^2)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (gamma0FullCuspidalFourierRepresentative_frequency_window N r Y hY i y hYy t) (sq_nonneg _))
    _ = (N:ℝ)⁻¹*(∫ x in Ioc 0 (N:ℝ), ∑ i ∈ s, i.1.re^2*‖F i (x+(N:ℝ)/2,y)‖^2) := by
      rw [integral_finsetSum s (fun i _ => hIw i),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_of_le hN.le,integral_const_mul]
      ring
    _ ≤ (N:ℝ)⁻¹*(∫ _x in Ioc 0 (N:ℝ), C^2) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hN.le)
    _ = C^2 := by
      rw [← intervalIntegral.integral_of_le hN.le,intervalIntegral.integral_const]
      simp only [sub_zero,smul_eq_mul]
      rw [← mul_assoc,inv_mul_cancel₀ hN.ne',one_mul]

theorem gamma0FullCuspidalFourierRepresentative_spectral_frequency_window_bound
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y a b : ℝ) (hY : 0 < Y) (ha : Y < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (t : Finset ℤ) (y : ℝ), y ∈ Icc a b →
      (∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R, ∑ n ∈ t,
        ‖gamma0FullCuspidalFourierRepresentative N r Y hY i n y‖^2) ≤ (C*(1+R))^2 := by
  obtain ⟨C,hC,hb⟩ := gamma0FullCuspidalFourierRepresentative_weighted_window_bound N r Y a b hY ha
  refine ⟨C,hC,?_⟩
  intro R t y hy
  have hpoint (i : Gamma0AllHeightSpectralIndex N)
      (hi : i ∈ gamma0AllHeightGradientSpectralCutoff N R) :
      (∑ n ∈ t, ‖gamma0FullCuspidalFourierRepresentative N r Y hY i n y‖^2) ≤
        (1+R)^2*(i.1.re^2*(∑ n ∈ t, ‖gamma0FullCuspidalFourierRepresentative N r Y hY i n y‖^2)) := by
    have hμ := gamma0AllHeightSpectralValue_pos N i
    have hval := (mem_gamma0AllHeightGradientSpectralCutoff N R i).mp hi
    change i.1.re⁻¹-1 ≤ R at hval
    have hinv : i.1.re⁻¹ ≤ 1+R := by linarith
    have hprod := mul_le_mul_of_nonneg_right hinv hμ.le
    rw [inv_mul_cancel₀ hμ.ne'] at hprod
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hprod 2
    rw [one_pow,mul_pow] at hs
    have hn : 0 ≤ ∑ n ∈ t,
        ‖gamma0FullCuspidalFourierRepresentative N r Y hY i n y‖^2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have ht := mul_le_mul_of_nonneg_right hs hn
    simpa only [one_mul,mul_assoc] using ht
  calc
    _ ≤ ∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R, (1+R)^2*(i.1.re^2*
        (∑ n ∈ t, ‖gamma0FullCuspidalFourierRepresentative N r Y hY i n y‖^2)) :=
      Finset.sum_le_sum hpoint
    _ = (1+R)^2*(∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R, i.1.re^2*
        (∑ n ∈ t, ‖gamma0FullCuspidalFourierRepresentative N r Y hY i n y‖^2)) := by rw [Finset.mul_sum]
    _ ≤ (1+R)^2*C^2 := mul_le_mul_of_nonneg_left (hb _ t y hy) (sq_nonneg _)
    _ = (C*(1+R))^2 := by ring

end ArtinMatthews
