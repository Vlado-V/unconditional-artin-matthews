module

public import ArtinMatthews.UnitTorusSmoothCoordinate


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute Fourier summability and reconstruction for a smooth periodic
real lift, using the product of the coordinate second-derivative factors. -/
namespace ArtinMatthews
open MeasureTheory UnitAddTorus Filter
open scoped BigOperators ContDiff
noncomputable section

local instance unitTorusSmoothFourierMeasure : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

variable (ι : Type*) [Fintype ι]

private theorem smoothFourierCoeff_sub (f g : C(UnitAddTorus ι, ℂ)) (n : ι → ℤ) :
    mFourierCoeff (f - g : C(UnitAddTorus ι, ℂ)) n = mFourierCoeff f n - mFourierCoeff g n := by
  simp only [mFourierCoeff, ContinuousMap.sub_apply, smul_sub]
  exact integral_sub (μ := unitTorusHaar ι)
    (((mFourier (-n)).continuous.smul f.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (((mFourier (-n)).continuous.smul g.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

private theorem smoothFourierCoeff_norm_le (f : C(UnitAddTorus ι, ℂ)) (n : ι → ℤ) :
    ‖mFourierCoeff f n‖ ≤ ‖f‖ := by
  change ‖∫ z, mFourier (-n) z • f z ∂unitTorusHaar ι‖ ≤ ‖f‖
  calc
    _ ≤ ∫ z, ‖mFourier (-n) z • f z‖ ∂unitTorusHaar ι := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : UnitAddTorus ι, ‖f‖ ∂unitTorusHaar ι := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (integrable_const _)
      apply Eventually.of_forall
      intro z
      have hz : ‖mFourier (-n) z‖ ≤ 1 := by
        simpa only [mFourier_norm] using (mFourier (-n)).norm_coe_le_norm z
      exact (norm_smul_le _ _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) hz).trans (f.norm_coe_le_norm z))
    _ = _ := by simp

private theorem exists_smoothFourier_weighted (f : C(UnitAddTorus ι, ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ι → ℝ => f (unitTorusUnitCellProjection ι x))) (s : Finset ι) :
    ∃ g : C(UnitAddTorus ι, ℂ),
      ContDiff ℝ ∞ (fun x : ι → ℝ => g (unitTorusUnitCellProjection ι x)) ∧
      ∀ n : ι → ℤ, mFourierCoeff g n =
        ((∏ j ∈ s, (1 + (2 * Real.pi * (n j : ℝ)) ^ 2) : ℝ) : ℂ) * mFourierCoeff f n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨f, hf, fun n => by simp⟩
  | @insert j s hj ih =>
    obtain ⟨g, hgs, hg⟩ := ih
    obtain ⟨d, _, hds, hd⟩ := unitTorus_smooth_coordinate_derivatives ι g hgs
    obtain ⟨dd, _, hdds, hdd⟩ := unitTorus_smooth_coordinate_derivatives ι (d j) (hds j)
    refine ⟨g - dd j, hgs.sub (hdds j), ?_⟩
    intro n
    have hsq : (2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) ^ 2 =
        -(((2 * Real.pi * (n j : ℝ)) ^ 2 : ℝ) : ℂ) := by
      calc
        _ = (2 * (Real.pi : ℂ) * (n j : ℂ)) ^ 2 * Complex.I ^ 2 := by ring
        _ = _ := by rw [Complex.I_sq]; push_cast; ring
    rw [smoothFourierCoeff_sub ι, hdd j, hd j, ← mul_assoc, ← pow_two, hsq, hg n,
      Finset.prod_insert hj, Complex.ofReal_mul]
    push_cast
    ring

private theorem smoothFourier_weight_summable :
    Summable (fun n : ℤ => (1 + (2 * Real.pi * (n : ℝ)) ^ 2)⁻¹) := by
  have hp : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by decide)
  have hq : Summable (fun n : ℤ => if n = 0 then 1 else 1 / (n : ℝ) ^ 2) :=
    hp.congr_cofinite (by
      filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
      simp only [hn, ite_false])
  refine hq.of_nonneg_of_le (fun _ => by positivity) ?_
  intro n
  by_cases hn : n = 0
  · subst n
    norm_num
  · simp only [hn, ite_false]
    rw [← one_div]
    apply one_div_le_one_div_of_le (sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hn))
    have hc : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hc₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hc 2
    rw [one_pow] at hc₂
    rw [mul_pow]
    nlinarith [mul_nonneg (sub_nonneg.mpr hc₂) (sq_nonneg (n : ℝ))]

private theorem smoothFourier_product_weight_summable :
    Summable (fun n : ι → ℤ => ∏ j, (1 + (2 * Real.pi * (n j : ℝ)) ^ 2)⁻¹) := by
  classical
  let w (n : ℤ) := (1 + (2 * Real.pi * (n : ℝ)) ^ 2)⁻¹
  have hw : Summable w := smoothFourier_weight_summable
  have hw₀ (n : ℤ) : 0 ≤ w n := by dsimp [w]; positivity
  apply summable_of_sum_le (c := ∏ _ : ι, ∑' n : ℤ, w n)
    (fun n => Finset.prod_nonneg (fun j _ => hw₀ (n j)))
  intro s
  let t (j : ι) := s.image (fun n => n j)
  calc
    ∑ n ∈ s, ∏ j, w (n j) ≤ ∑ n ∈ Fintype.piFinset t, ∏ j, w (n j) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun n hn => Fintype.mem_piFinset.mpr fun j => Finset.mem_image_of_mem _ hn)
        (fun n _ _ => Finset.prod_nonneg (fun j _ => hw₀ (n j)))
    _ = ∏ j, ∑ k ∈ t j, w k := (Finset.prod_univ_sum t (fun _ => w)).symm
    _ ≤ _ := Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun k _ => hw₀ k)
      (fun j _ => hw.sum_le_tsum (t j) (fun k _ => hw₀ k))

theorem unitTorus_norm_mFourierCoeff_le_product (f : UnitAddTorus ι → ℂ) (hf : Continuous f)
    (hsmooth : ContDiff ℝ ∞ (fun x : ι → ℝ => f (unitTorusUnitCellProjection ι x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ι → ℤ,
      ‖mFourierCoeff f n‖ ≤ C * ∏ j, (1 + (2 * Real.pi * (n j : ℝ)) ^ 2)⁻¹ := by
  let F : C(UnitAddTorus ι, ℂ) := ⟨f, hf⟩
  obtain ⟨g, _, hg⟩ := exists_smoothFourier_weighted ι F hsmooth Finset.univ
  refine ⟨‖g‖, norm_nonneg _, ?_⟩
  intro n
  let D := ∏ j : ι, (1 + (2 * Real.pi * (n j : ℝ)) ^ 2)
  have hD : 0 < D := Finset.prod_pos (fun _ _ => by positivity)
  have hb := smoothFourierCoeff_norm_le ι g n
  rw [hg n, norm_mul, Complex.norm_real, Real.norm_of_nonneg hD.le] at hb
  rw [Finset.prod_inv_distrib, ← div_eq_mul_inv]
  apply (le_div_iff₀ hD).mpr
  rw [mul_comm]
  exact hb

theorem unitTorus_summable_norm_mFourierCoeff_of_smooth (f : UnitAddTorus ι → ℂ) (hf : Continuous f)
    (hsmooth : ContDiff ℝ ∞ (fun x : ι → ℝ => f (unitTorusUnitCellProjection ι x))) :
    Summable (fun n : ι → ℤ => ‖mFourierCoeff f n‖) := by
  obtain ⟨C, _, hC⟩ := unitTorus_norm_mFourierCoeff_le_product ι f hf hsmooth
  exact ((smoothFourier_product_weight_summable ι).mul_left C).of_nonneg_of_le
    (fun _ => norm_nonneg _) hC

theorem unitTorus_summable_mFourierCoeff_of_smooth (f : UnitAddTorus ι → ℂ) (hf : Continuous f)
    (hsmooth : ContDiff ℝ ∞ (fun x : ι → ℝ => f (unitTorusUnitCellProjection ι x))) :
    Summable (mFourierCoeff f) :=
  (unitTorus_summable_norm_mFourierCoeff_of_smooth ι f hf hsmooth).of_norm

theorem unitTorus_hasSum_mFourier_of_smooth (f : UnitAddTorus ι → ℂ) (hf : Continuous f)
    (hsmooth : ContDiff ℝ ∞ (fun x : ι → ℝ => f (unitTorusUnitCellProjection ι x)))
    (z : UnitAddTorus ι) : HasSum (fun n => mFourier n z * mFourierCoeff f n) (f z) := by
  let F : C(UnitAddTorus ι, ℂ) := ⟨f, hf⟩
  have h := hasSum_mFourier_series_apply_of_summable (f := F)
    (unitTorus_summable_mFourierCoeff_of_smooth ι f hf hsmooth) z
  refine HasSum.congr_fun h (fun n => ?_)
  change mFourier n z * mFourierCoeff f n = mFourierCoeff f n * mFourier n z
  exact mul_comm _ _

end
end ArtinMatthews
