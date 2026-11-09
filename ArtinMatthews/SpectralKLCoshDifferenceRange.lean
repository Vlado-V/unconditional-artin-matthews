module

public import ArtinMatthews.SpectralKLRangeCutoff
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! The actual exponential differences lie in the completed KL synthesis
range. Both spectral L2 and physical pointwise cutoff limits are proved. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology

namespace ArtinMatthews

theorem spectral_Lp_limit_ae_of_pointwise {μ : Measure ℝ}
    (F : ℕ → Lp ℂ 2 μ) (U : Lp ℂ 2 μ) (hF : Tendsto F atTop (𝓝 U))
    (f : ℕ → ℝ → ℂ) (hf : ∀ n, F n =ᵐ[μ] f n) (g : ℝ → ℂ)
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    U =ᵐ[μ] g := by
  obtain ⟨ns,hns,hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, F n x = f n x := ae_all_iff.mpr hf
  filter_upwards [hall,hsub,hpoint] with x hx hs hp
  have heq : (fun n => F (ns n) x) = (fun n => f (ns n) x) := funext (fun n => hx (ns n))
  rw [heq] at hs
  exact tendsto_nhds_unique hs (hp.comp hns.tendsto_atTop)

theorem spectralKLCosineDifferenceData_weight_norm (u v t : ℝ) (ht : 0 < t) :
    ‖(spectralKLPlancherelWeight t : ℂ)*spectralKLCosineDifferenceData u v t‖ ≤ 4/Real.pi := by
  rw [spectralKLCosineDifferenceData_weight_mul u v t ht,Complex.norm_real,Real.norm_eq_abs,abs_mul,
    abs_of_pos (div_pos two_pos Real.pi_pos)]
  have hcos : |Real.cos (t*u)-Real.cos (t*v)| ≤ 2 := by
    calc
      _ ≤ |Real.cos (t*u)|+|Real.cos (t*v)| := abs_sub _ _
      _ ≤ 1+1 := add_le_add (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
      _ = _ := by norm_num
  calc
    _ ≤ (2/Real.pi)*2 := mul_le_mul_of_nonneg_left hcos (div_pos two_pos Real.pi_pos).le
    _ = _ := by ring

theorem spectralKLCosineDifferenceCutoff_synthesis_pointwise {x : ℝ} (hx : 0 < x) (u v : ℝ) :
    Tendsto (fun n => spectralKLWeightedSynthesis (spectralKLCosineDifferenceCutoff u v n) x) atTop
      (𝓝 (Complex.exp (-(x*Real.cosh u) : ℝ)-Complex.exp (-(x*Real.cosh v) : ℝ))) := by
  have hK := schlafliBesselK_imaginary_order_integrable hx
  have hlim : Tendsto (fun n => ∫ t in Ioi (0 : ℝ),
      schlafliBesselK ((t : ℂ)*Complex.I) x*spectralKLCosineDifferenceCutoff u v n t*
        (spectralKLPlancherelWeight t : ℂ)) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) x*
        spectralKLCosineDifferenceData u v t*(spectralKLPlancherelWeight t : ℂ))) := by
    apply tendsto_integral_of_dominated_convergence (fun t : ℝ => (4/Real.pi)*‖schlafliBesselK ((t : ℂ)*Complex.I) x‖)
    · intro n
      exact (hK.aestronglyMeasurable.restrict.mul
        (spectralKLCosineDifferenceCutoff_test u v n).1.continuous.aestronglyMeasurable).mul
          (Complex.continuous_ofReal.comp spectralKLPlancherelWeight_continuous).aestronglyMeasurable
    · exact (hK.norm.const_mul (4/Real.pi)).restrict
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hη : ‖(spectralKLRangeCutoff n t : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real,Real.norm_of_nonneg (spectralKLRangeCutoff_bounds n t).1]
        exact (spectralKLRangeCutoff_bounds n t).2
      rw [show schlafliBesselK ((t : ℂ)*Complex.I) x*spectralKLCosineDifferenceCutoff u v n t*
          (spectralKLPlancherelWeight t : ℂ) = (spectralKLRangeCutoff n t : ℂ)*
          schlafliBesselK ((t : ℂ)*Complex.I) x*
          ((spectralKLPlancherelWeight t : ℂ)*spectralKLCosineDifferenceData u v t) by
            unfold spectralKLCosineDifferenceCutoff; ring]
      rw [norm_mul,norm_mul]
      calc
        _ ≤ (1*‖schlafliBesselK ((t : ℂ)*Complex.I) x‖)*(4/Real.pi) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hη (norm_nonneg _))
            (spectralKLCosineDifferenceData_weight_norm u v t ht) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply tendsto_const_nhds.congr'
      filter_upwards [spectralKLRangeCutoff_eventually_one ht] with n hn
      simp [spectralKLCosineDifferenceCutoff,hn]
  have heq : (∫ t in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) x*
      spectralKLCosineDifferenceData u v t*(spectralKLPlancherelWeight t : ℂ)) =
      Complex.exp (-(x*Real.cosh u) : ℝ)-Complex.exp (-(x*Real.cosh v) : ℝ) := by
    calc
      _ = (2/Real.pi : ℝ) • (∫ t in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) x*
          ((Real.cos (t*u)-Real.cos (t*v) : ℝ) : ℂ)) := by
        rw [← integral_smul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [Complex.real_smul]
        calc
          _ = schlafliBesselK ((t : ℂ)*Complex.I) x*
              ((spectralKLPlancherelWeight t : ℂ)*spectralKLCosineDifferenceData u v t) := by ring
          _ = _ := by rw [spectralKLCosineDifferenceData_weight_mul u v t ht,Complex.ofReal_mul]; ring
      _ = _ := schlafliBesselK_cosh_fourier_difference hx u v
  simpa only [spectralKLWeightedSynthesis,heq] using hlim

theorem spectralKLCompletedSynthesis_cosineDifference_ae (u v : ℝ) :
    spectralKLCompletedSynthesis ((spectralKLCosineDifferenceData_memLp u v).toLp
      (spectralKLCosineDifferenceData u v)) =ᵐ[spectralKLPhysicalMeasure]
      (fun x => Complex.exp (-(x*Real.cosh u) : ℝ)-Complex.exp (-(x*Real.cosh v) : ℝ)) := by
  have hLp : Tendsto (fun n => spectralKLTestSynthesis (spectralKLCosineDifferenceTest u v n)) atTop
      (𝓝 (spectralKLCompletedSynthesis ((spectralKLCosineDifferenceData_memLp u v).toLp
        (spectralKLCosineDifferenceData u v)))) := by
    have h := spectralKLCompletedSynthesis.continuous.continuousAt.tendsto.comp
      (spectralKLCosineDifferenceTest_tendsto u v)
    simpa only [Function.comp_def,spectralKLCompletedSynthesis_test] using h
  apply spectral_Lp_limit_ae_of_pointwise _ _ hLp
    (fun n => spectralKLWeightedSynthesis (spectralKLCosineDifferenceCutoff u v n))
    (fun n => spectralKLTestSynthesis_coe (spectralKLCosineDifferenceTest u v n))
  filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
  exact spectralKLCosineDifferenceCutoff_synthesis_pointwise hx u v

theorem spectralKLCoshDifference_memLp (u v : ℝ) :
    MemLp (fun x : ℝ => Complex.exp (-(x*Real.cosh u) : ℝ)-Complex.exp (-(x*Real.cosh v) : ℝ))
      2 spectralKLPhysicalMeasure :=
  (memLp_congr_ae (spectralKLCompletedSynthesis_cosineDifference_ae u v)).mp
    (Lp.memLp (spectralKLCompletedSynthesis ((spectralKLCosineDifferenceData_memLp u v).toLp
      (spectralKLCosineDifferenceData u v))))

theorem spectralKLCoshDifference_mem_range (u v : ℝ) :
    (spectralKLCoshDifference_memLp u v).toLp
      (fun x : ℝ => Complex.exp (-(x*Real.cosh u) : ℝ)-Complex.exp (-(x*Real.cosh v) : ℝ)) ∈
        Set.range spectralKLCompletedSynthesis := by
  refine ⟨(spectralKLCosineDifferenceData_memLp u v).toLp (spectralKLCosineDifferenceData u v),?_⟩
  apply Lp.ext
  exact (spectralKLCompletedSynthesis_cosineDifference_ae u v).trans
    (MemLp.coeFn_toLp (spectralKLCoshDifference_memLp u v)).symm

end ArtinMatthews
