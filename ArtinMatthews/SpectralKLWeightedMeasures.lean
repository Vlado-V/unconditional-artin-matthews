module

public import ArtinMatthews.SpectralKLCompactIsometry
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition


set_option backward.privateInPublic true
@[expose] public section

/-! Literal positive spectral and physical KL measures, and the weighted
integrals used to connect the proved compact synthesis identity with Lp. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace ArtinMatthews

def spectralKLPositiveWeightMeasure (w : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (w t))

def spectralKLSpectralMeasure : Measure ℝ := spectralKLPositiveWeightMeasure spectralKLPlancherelWeight

def spectralKLPhysicalMeasure : Measure ℝ := spectralKLPositiveWeightMeasure (fun x => x⁻¹)

theorem spectralKLPositiveWeightMeasure_ae_pos (w : ℝ → ℝ) :
    ∀ᵐ t ∂spectralKLPositiveWeightMeasure w, 0 < t :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

theorem spectralKLPositiveWeightMeasure_integrable_iff (w H : ℝ → ℝ) (hw : Measurable w)
    (hp : ∀ t : ℝ, 0 < t → 0 ≤ w t) :
    Integrable H (spectralKLPositiveWeightMeasure w) ↔
      IntegrableOn (fun t => w t*H t) (Ioi (0 : ℝ)) := by
  unfold spectralKLPositiveWeightMeasure
  have hwd : Measurable (fun t : ℝ => ENNReal.ofReal (w t)) := ENNReal.measurable_ofReal.comp hw
  have hfin : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ENNReal.ofReal (w t) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  apply (integrable_withDensity_iff_integrable_smul' (μ := volume.restrict (Ioi (0 : ℝ)))
    (g := H) hwd hfin).trans
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.toReal_ofReal (hp t ht),smul_eq_mul]

theorem spectralKLPositiveWeightMeasure_integral (w H : ℝ → ℝ) (hw : Measurable w)
    (hp : ∀ t : ℝ, 0 < t → 0 ≤ w t) :
    (∫ t, H t ∂spectralKLPositiveWeightMeasure w) = ∫ t in Ioi (0 : ℝ), w t*H t := by
  unfold spectralKLPositiveWeightMeasure
  have hwd : Measurable (fun t : ℝ => ENNReal.ofReal (w t)) := ENNReal.measurable_ofReal.comp hw
  have hfin : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ENNReal.ofReal (w t) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [integral_withDensity_eq_integral_toReal_smul (μ := volume.restrict (Ioi (0 : ℝ))) hwd hfin H]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.toReal_ofReal (hp t ht),smul_eq_mul]

instance spectralKLSpectralMeasure_locallyFinite : IsLocallyFiniteMeasure spectralKLSpectralMeasure := by
  have : IsLocallyFiniteMeasure (volume.withDensity (fun t : ℝ =>
      ENNReal.ofReal (spectralKLPlancherelWeight t))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal spectralKLPlancherelWeight_continuous
  unfold spectralKLSpectralMeasure spectralKLPositiveWeightMeasure
  rw [← restrict_withDensity measurableSet_Ioi]
  infer_instance

theorem spectralKLSpectralMeasure_memLp_compact (g : ℝ → ℂ) (hg : Continuous g)
    (hgc : HasCompactSupport g) : MemLp g 2 spectralKLSpectralMeasure :=
  hg.memLp_of_hasCompactSupport hgc

theorem spectral_Lp_norm_sq {μ : Measure ℝ} (u : Lp ℂ 2 μ) :
    ‖u‖^2 = ∫ t : ℝ, ‖u t‖^2 ∂μ := by
  have hi : Integrable (fun t : ℝ => inner ℂ (u t) (u t)) μ := by
    exact memLp_one_iff_integrable.mp (L2.eLpNorm_inner_lt_top u u)
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def,← integral_re hi]
  apply integral_congr_ae
  filter_upwards with t
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (u t)).symm

theorem spectral_toLp_norm_sq {μ : Measure ℝ} (g : ℝ → ℂ) (hg : MemLp g 2 μ) :
    ‖hg.toLp g‖^2 = ∫ t : ℝ, ‖g t‖^2 ∂μ := by
  rw [spectral_Lp_norm_sq]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with t ht
  rw [ht]

theorem spectralKLWeightedSynthesis_memLp (g : ℝ → ℂ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    MemLp (spectralKLWeightedSynthesis g) 2 spectralKLPhysicalMeasure := by
  let f : ℝ → ℂ := fun t => (spectralKLPlancherelWeight t : ℂ)*g t
  have hf : Continuous f := (Complex.continuous_ofReal.comp spectralKLPlancherelWeight_continuous).mul hg
  have hm0 : AEStronglyMeasurable (spectralKLSynthesis f) spectralKLPhysicalMeasure :=
    (spectralKLSynthesis_stronglyMeasurable f hf).aestronglyMeasurable
  have hm : AEStronglyMeasurable (spectralKLWeightedSynthesis g) spectralKLPhysicalMeasure := by
    apply hm0.congr
    filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
    exact (spectralKLWeightedSynthesis_eq g hgp hx).symm
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  rw [spectralKLPhysicalMeasure,spectralKLPositiveWeightMeasure_integrable_iff _ _ (by fun_prop)
    (fun t ht => inv_nonneg.mpr ht.le)]
  apply (spectralKLCompact_synthesis_isometry g hg hgc hgp).1.congr
  filter_upwards with x
  simp only [div_eq_mul_inv]
  ring

theorem spectralKLWeightedSynthesis_toLp_norm (g : ℝ → ℂ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    ‖(spectralKLWeightedSynthesis_memLp g hg hgc hgp).toLp (spectralKLWeightedSynthesis g)‖ =
      ‖(spectralKLSpectralMeasure_memLp_compact g hg hgc).toLp g‖ := by
  have hnorm :
      ‖(spectralKLWeightedSynthesis_memLp g hg hgc hgp).toLp (spectralKLWeightedSynthesis g)‖^2 =
      ‖(spectralKLSpectralMeasure_memLp_compact g hg hgc).toLp g‖^2 := by
    rw [spectral_toLp_norm_sq,spectral_toLp_norm_sq,
      spectralKLPhysicalMeasure,spectralKLSpectralMeasure,
      spectralKLPositiveWeightMeasure_integral _ _ (by fun_prop) (fun t ht => inv_nonneg.mpr ht.le),
      spectralKLPositiveWeightMeasure_integral _ _ spectralKLPlancherelWeight_continuous.measurable
        (fun t ht => (spectralKLPlancherelWeight_pos ht).le)]
    convert (spectralKLCompact_synthesis_isometry g hg hgc hgp).2 using 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    simp only [div_eq_mul_inv]
    ring
  nlinarith [norm_nonneg ((spectralKLWeightedSynthesis_memLp g hg hgc hgp).toLp (spectralKLWeightedSynthesis g)),
    norm_nonneg ((spectralKLSpectralMeasure_memLp_compact g hg hgc).toLp g)]

end ArtinMatthews
