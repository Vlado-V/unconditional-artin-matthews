module

public import ArtinMatthews.SpectralAmbientGreenMoments
public import ArtinMatthews.SpectralEisensteinSeedAnalysis


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Green multiplier on the normalized Eisenstein channels.
Its bound and self-adjointness come from its explicit real multiplier. -/
noncomputable section
open Set Filter MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

def gamma0EisensteinGreenWeight (t : ℝ) : ℂ :=
  gamma0EnergyGreenWeight (spectralStoneEnergyFromFrequency t)

theorem gamma0EisensteinGreenWeight_measurable : Measurable gamma0EisensteinGreenWeight :=
  gamma0EnergyGreenWeight_measurable.comp (continuous_const.add (continuous_id.pow 2)).measurable

theorem gamma0EisensteinGreenWeight_conj (t : ℝ) :
    (starRingEnd ℂ) (gamma0EisensteinGreenWeight t)=gamma0EisensteinGreenWeight t := by
  rw [gamma0EisensteinGreenWeight,gamma0EnergyGreenWeight_eq_real,Complex.conj_ofReal]

theorem gamma0EisensteinGreenWeight_norm_le (t : ℝ) : ‖gamma0EisensteinGreenWeight t‖≤1 := by
  have hD : 1 ≤ spectralStoneEnergyFromFrequency t+1 := by
    unfold spectralStoneEnergyFromFrequency
    nlinarith [sq_nonneg t]
  have hpos : 0<spectralStoneEnergyFromFrequency t+1 := zero_lt_one.trans_le hD
  rw [gamma0EisensteinGreenWeight,gamma0EnergyGreenWeight_eq_real,Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  simpa only [one_div,inv_one] using one_div_le_one_div_of_le zero_lt_one hD

theorem gamma0EisensteinGreenMultiply_memLp (f : Lp ℂ 2 gamma0EisensteinSpectralMeasure) :
    MemLp (fun t => gamma0EisensteinGreenWeight t*f t) 2 gamma0EisensteinSpectralMeasure := by
  apply (Lp.memLp f).of_le_mul (c:=1)
    (gamma0EisensteinGreenWeight_measurable.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact ae_of_all _ (fun t => by
    change ‖gamma0EisensteinGreenWeight t*f t‖≤1*‖f t‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (gamma0EisensteinGreenWeight_norm_le t) (norm_nonneg (f t)))

def gamma0EisensteinGreenMultiply (f : Lp ℂ 2 gamma0EisensteinSpectralMeasure) :
    Lp ℂ 2 gamma0EisensteinSpectralMeasure :=
  (gamma0EisensteinGreenMultiply_memLp f).toLp _

theorem gamma0EisensteinGreenMultiply_ae (f : Lp ℂ 2 gamma0EisensteinSpectralMeasure) :
    gamma0EisensteinGreenMultiply f=ᵐ[gamma0EisensteinSpectralMeasure]
      fun t => gamma0EisensteinGreenWeight t*f t :=
  (gamma0EisensteinGreenMultiply_memLp f).coeFn_toLp

theorem gamma0EisensteinGreenMultiply_add (f g : Lp ℂ 2 gamma0EisensteinSpectralMeasure) :
    gamma0EisensteinGreenMultiply (f+g)=gamma0EisensteinGreenMultiply f+gamma0EisensteinGreenMultiply g := by
  apply Lp.ext
  filter_upwards [gamma0EisensteinGreenMultiply_ae (f+g),gamma0EisensteinGreenMultiply_ae f,
    gamma0EisensteinGreenMultiply_ae g,Lp.coeFn_add f g,
    Lp.coeFn_add (gamma0EisensteinGreenMultiply f) (gamma0EisensteinGreenMultiply g)] with t hs hf hg hfg hm
  rw [hs,hm]
  simp only [Pi.add_apply]
  rw [hf,hg,hfg]
  simp only [Pi.add_apply]
  ring

theorem gamma0EisensteinGreenMultiply_smul (c : ℂ) (f : Lp ℂ 2 gamma0EisensteinSpectralMeasure) :
    gamma0EisensteinGreenMultiply (c • f)=c • gamma0EisensteinGreenMultiply f := by
  apply Lp.ext
  filter_upwards [gamma0EisensteinGreenMultiply_ae (c • f),gamma0EisensteinGreenMultiply_ae f,
    Lp.coeFn_smul c f,Lp.coeFn_smul c (gamma0EisensteinGreenMultiply f)] with t hs hf hcf hm
  rw [hs,hm]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hf,hcf]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

theorem gamma0EisensteinGreenMultiply_norm_le (f : Lp ℂ 2 gamma0EisensteinSpectralMeasure) :
    ‖gamma0EisensteinGreenMultiply f‖≤‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [gamma0EisensteinGreenMultiply_ae f] with t ht
  rw [ht,norm_mul]
  exact (mul_le_mul_of_nonneg_right (gamma0EisensteinGreenWeight_norm_le t) (norm_nonneg (f t))).trans_eq (one_mul _)

def gamma0EisensteinGreenScalarOperator :
    Lp ℂ 2 gamma0EisensteinSpectralMeasure →L[ℂ] Lp ℂ 2 gamma0EisensteinSpectralMeasure :=
  LinearMap.mkContinuous
    { toFun := gamma0EisensteinGreenMultiply
      map_add' := gamma0EisensteinGreenMultiply_add
      map_smul' := gamma0EisensteinGreenMultiply_smul }
    1 (fun f => by
      change ‖gamma0EisensteinGreenMultiply f‖≤1*‖f‖
      simpa only [one_mul] using gamma0EisensteinGreenMultiply_norm_le f)

theorem gamma0EisensteinGreenScalarOperator_selfAdjoint : IsSelfAdjoint gamma0EisensteinGreenScalarOperator := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gamma0EisensteinGreenMultiply_ae f,gamma0EisensteinGreenMultiply_ae g] with t hf hg
  change inner ℂ (gamma0EisensteinGreenMultiply f t) (g t)=inner ℂ (f t) (gamma0EisensteinGreenMultiply g t)
  rw [hf,hg]
  rw [RCLike.inner_apply,RCLike.inner_apply,map_mul,gamma0EisensteinGreenWeight_conj]
  ring

def gamma0EisensteinGreenMultiplier (N : ℕ) [NeZero N] :
    Gamma0EisensteinSpectralSpace N →L[ℂ] Gamma0EisensteinSpectralSpace N :=
  (PiLp.continuousLinearEquiv 2 ℂ
    (fun _ : Gamma0EisensteinCuspClasses N => Lp ℂ 2 gamma0EisensteinSpectralMeasure)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi (fun i => gamma0EisensteinGreenScalarOperator.comp (ContinuousLinearMap.proj i))).comp
      (PiLp.continuousLinearEquiv 2 ℂ
        (fun _ : Gamma0EisensteinCuspClasses N => Lp ℂ 2 gamma0EisensteinSpectralMeasure)).toContinuousLinearMap)

theorem gamma0EisensteinGreenMultiplier_apply (N : ℕ) [NeZero N]
    (f : Gamma0EisensteinSpectralSpace N) (i : Gamma0EisensteinCuspClasses N) :
    gamma0EisensteinGreenMultiplier N f i=gamma0EisensteinGreenMultiply (f i) := rfl

theorem gamma0EisensteinGreenMultiplier_norm_le (N : ℕ) [NeZero N] (f : Gamma0EisensteinSpectralSpace N) :
    ‖gamma0EisensteinGreenMultiplier N f‖≤‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) (gamma0EisensteinGreenMultiply_norm_le (f i)) 2

theorem gamma0EisensteinGreenMultiplier_selfAdjoint (N : ℕ) [NeZero N] :
    IsSelfAdjoint (gamma0EisensteinGreenMultiplier N) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change (∑ i,inner ℂ (gamma0EisensteinGreenScalarOperator (f i)) (g i))=
    ∑ i,inner ℂ (f i) (gamma0EisensteinGreenScalarOperator (g i))
  apply Finset.sum_congr rfl
  intro i _
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp gamma0EisensteinGreenScalarOperator_selfAdjoint) (f i) (g i)

end ArtinMatthews
