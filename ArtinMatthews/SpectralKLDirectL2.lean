module

public import ArtinMatthews.SpectralKLDirectBounds
public import ArtinMatthews.SpectralKLNoncompactSynthesis


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter
open scoped ContDiff
noncomputable section

theorem spectralKLDirectRapid_square_bound (F : ℝ → ℂ) (hrapid : SpectralKLDirectRapid F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      |spectralKLPlancherelWeight t| * ‖F t‖ ^ 2 ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := hrapid 1
  refine ⟨(2 / Real.pi ^ 2) * C ^ 2, by positivity, ?_⟩
  intro t
  let u := 1 + t ^ 2
  let E := Real.exp (Real.pi * |t| / 2)
  have hu : 0 < u := by dsimp [u]; positivity
  have hE : 0 < E := Real.exp_pos _
  have hf : E * ‖F t‖ ≤ C / u := by
    apply (le_div_iff₀ hu).mpr
    simpa only [pow_one, u, E, mul_assoc, mul_comm, mul_left_comm] using hb t
  have hs : (E * ‖F t‖) ^ 2 ≤ (C / u) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hf 2
  have hw : |spectralKLPlancherelWeight t| ≤ (2 / Real.pi ^ 2) * |t| * E ^ 2 := by
    have heq : E ^ 2 = Real.exp (Real.pi * |t|) := by
      dsimp [E]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact spectralKLPlancherelWeight_abs_bound t
  have ht : |t| ≤ u := by dsimp [u]; nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  calc
    _ ≤ ((2 / Real.pi ^ 2) * |t| * E ^ 2) * ‖F t‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (2 / Real.pi ^ 2) * |t| * (E * ‖F t‖) ^ 2 := by ring
    _ ≤ (2 / Real.pi ^ 2) * |t| * (C / u) ^ 2 := by gcongr
    _ ≤ (2 / Real.pi ^ 2) * u * (C / u) ^ 2 := by gcongr
    _ = _ := by
      field_simp
      dsimp only [u]
      ring

theorem spectralKLDirectData_memLp (F : ℝ → ℂ) (hF : Continuous F)
    (hrapid : SpectralKLDirectRapid F) : MemLp F 2 spectralKLSpectralMeasure := by
  apply (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mpr
  change Integrable _ (spectralKLPositiveWeightMeasure spectralKLPlancherelWeight)
  apply (spectralKLPositiveWeightMeasure_integrable_iff spectralKLPlancherelWeight
    (fun t => ‖F t‖ ^ 2) spectralKLPlancherelWeight_continuous.measurable
      (fun t ht => (spectralKLPlancherelWeight_pos ht).le)).mpr
  obtain ⟨C, _, hb⟩ := spectralKLDirectRapid_square_bound F hrapid
  have hm : AEStronglyMeasurable (fun t => spectralKLPlancherelWeight t * ‖F t‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) := by
    exact (spectralKLPlancherelWeight_continuous.mul (hF.norm.pow 2)).aestronglyMeasurable
  apply (integrable_inv_one_add_sq.const_mul C).restrict.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_of_nonneg (mul_nonneg (spectralKLPlancherelWeight_pos ht).le (sq_nonneg _))]
  simpa only [abs_of_nonneg (spectralKLPlancherelWeight_pos ht).le, div_eq_mul_inv] using hb t

theorem spectralKLDirectSynthesis_measurable (F : ℝ → ℂ) (hF : Continuous F)
    (hrapid : SpectralKLDirectRapid F) : Measurable (spectralKLDirectSynthesis F) := by
  have hcont := spectralKLDirectSynthesis_continuousOn F hF hrapid
  have hzero : ContinuousOn (spectralKLDirectSynthesis F) (Ioi (0 : ℝ))ᶜ := by
    apply (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℂ)) ((Ioi (0 : ℝ))ᶜ)).congr
    intro x hx
    change ¬0 < x at hx
    simp only [spectralKLDirectSynthesis, ite_eq_right hx]
  have hm := hcont.measurable_piecewise hzero measurableSet_Ioi
  simpa only [Set.piecewise_same] using hm

theorem spectralKLDirectSynthesis_inverse_ae (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ioi (0 : ℝ))) (hFc : Continuous F)
    (hrapid : SpectralKLDirectRapid F) :
    spectralKLCompletedSynthesis ((spectralKLDirectData_memLp F hFc hrapid).toLp F) =ᵐ[spectralKLPhysicalMeasure]
      spectralKLDirectSynthesis F := by
  have ha := spectralKLCompletedSynthesis_integral_ae F hF (spectralKLDirectData_memLp F hFc hrapid)
    (fun x hx => (spectralKLDirectSynthesis_integrable F hFc hrapid hx).integrableOn)
  filter_upwards [ha, spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx hxp
  simpa only [spectralKLDirectSynthesis, ite_eq_left hxp] using hx

theorem spectralKLDirectSynthesis_memLp (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ioi (0 : ℝ))) (hFc : Continuous F)
    (hrapid : SpectralKLDirectRapid F) : MemLp (spectralKLDirectSynthesis F) 2 spectralKLPhysicalMeasure :=
  (memLp_congr_ae (spectralKLDirectSynthesis_inverse_ae F hF hFc hrapid)).mp (Lp.memLp _)

end
end ArtinMatthews
