module

public import ArtinMatthews.SpectralPositiveSmoothDensity


set_option backward.privateInPublic true
@[expose] public section

/-! Compact positive continuous tests are dense in physical L2(dx/x).
This is proved by the literal sqrt(x) change of weight from restricted
Lebesgue L2, not assumed as a range hypothesis. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace ArtinMatthews

def spectralKLPhysicalSqrtLift (g : ℝ → ℂ) (x : ℝ) : ℂ := (Real.sqrt x : ℂ)*g x

def spectralKLPhysicalSqrtDown (H : ℝ → ℂ) (x : ℝ) : ℂ := H x/(Real.sqrt x : ℂ)

theorem spectralKLPhysical_sqrt_norm (x : ℝ) (hx : 0 < x) (z : ℂ) :
    x⁻¹*‖(Real.sqrt x : ℂ)*z‖^2 = ‖z‖^2 := by
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt hx.le]
  field_simp

theorem spectralKLPhysical_sqrt_div_norm (x : ℝ) (hx : 0 < x) (z : ℂ) :
    ‖z/(Real.sqrt x : ℂ)‖^2 = x⁻¹*‖z‖^2 := by
  rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),div_pow,Real.sq_sqrt hx.le]
  ring

theorem spectralKLPhysicalSqrtDown_memLp (H : ℝ → ℂ) (hHm : StronglyMeasurable H)
    (hH : MemLp H 2 spectralKLPhysicalMeasure) :
    MemLp (spectralKLPhysicalSqrtDown H) 2 spectralKLPositiveLebesgueMeasure := by
  have hm : AEStronglyMeasurable (spectralKLPhysicalSqrtDown H) spectralKLPositiveLebesgueMeasure := by
    unfold spectralKLPhysicalSqrtDown
    exact (hHm.measurable.div (Complex.continuous_ofReal.comp Real.continuous_sqrt).measurable).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := (memLp_two_iff_integrable_sq_norm hH.aestronglyMeasurable).mp hH
  have hw : IntegrableOn (fun x : ℝ => x⁻¹*‖H x‖^2) (Ioi 0) :=
    (spectralKLPositiveWeightMeasure_integrable_iff (fun x => x⁻¹) (fun x => ‖H x‖^2)
      (by fun_prop) (fun x hx => inv_nonneg.mpr hx.le)).mp hi
  apply hw.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (spectralKLPhysical_sqrt_div_norm x hx (H x)).symm

theorem spectralKLPhysicalSqrtLift_memLp (g : ℝ → ℂ) (hgm : Measurable g)
    (hg : MemLp g 2 spectralKLPositiveLebesgueMeasure) :
    MemLp (spectralKLPhysicalSqrtLift g) 2 spectralKLPhysicalMeasure := by
  have hm : AEStronglyMeasurable (spectralKLPhysicalSqrtLift g) spectralKLPhysicalMeasure :=
    ((Complex.continuous_ofReal.comp Real.continuous_sqrt).measurable.mul hgm).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (spectralKLPositiveWeightMeasure_integrable_iff (fun x => x⁻¹)
    (fun x => ‖spectralKLPhysicalSqrtLift g x‖^2) (by fun_prop) (fun x hx => inv_nonneg.mpr hx.le)).mpr
  have hi := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (spectralKLPhysical_sqrt_norm x hx (g x)).symm

theorem spectralKLPhysicalSqrt_norm_sub (H g : ℝ → ℂ) (hHm : StronglyMeasurable H)
    (hH : MemLp H 2 spectralKLPhysicalMeasure) (hgm : Measurable g)
    (hg : MemLp g 2 spectralKLPositiveLebesgueMeasure) :
    ‖(spectralKLPhysicalSqrtLift_memLp g hgm hg).toLp (spectralKLPhysicalSqrtLift g)-hH.toLp H‖ =
      ‖hg.toLp g-(spectralKLPhysicalSqrtDown_memLp H hHm hH).toLp (spectralKLPhysicalSqrtDown H)‖ := by
  have hsq :
      ‖(spectralKLPhysicalSqrtLift_memLp g hgm hg).toLp (spectralKLPhysicalSqrtLift g)-hH.toLp H‖^2 =
      ‖hg.toLp g-(spectralKLPhysicalSqrtDown_memLp H hHm hH).toLp (spectralKLPhysicalSqrtDown H)‖^2 := by
    rw [← MemLp.toLp_sub,← MemLp.toLp_sub,spectral_toLp_norm_sq,spectral_toLp_norm_sq]
    rw [spectralKLPhysicalMeasure,spectralKLPositiveWeightMeasure_integral _ _ (by fun_prop)
      (fun x hx => inv_nonneg.mpr hx.le)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hs : (Real.sqrt x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
    have heq : spectralKLPhysicalSqrtLift g x-H x =
        (Real.sqrt x : ℂ)*(g x-spectralKLPhysicalSqrtDown H x) := by
      unfold spectralKLPhysicalSqrtLift spectralKLPhysicalSqrtDown
      field_simp
    dsimp only [Pi.sub_apply]
    rw [heq,spectralKLPhysical_sqrt_norm x hx]
  nlinarith [norm_nonneg ((spectralKLPhysicalSqrtLift_memLp g hgm hg).toLp (spectralKLPhysicalSqrtLift g)-hH.toLp H),
    norm_nonneg (hg.toLp g-(spectralKLPhysicalSqrtDown_memLp H hHm hH).toLp (spectralKLPhysicalSqrtDown H))]

theorem spectralKLPhysicalMeasure_dense_compact_positive :
    Dense {u : Lp ℂ 2 spectralKLPhysicalMeasure | ∃ f : ℝ → ℂ,
      u =ᵐ[spectralKLPhysicalMeasure] f ∧ HasCompactSupport f ∧ Continuous f ∧
        tsupport f ⊆ Ioi (0 : ℝ)} := by
  intro u
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let H : ℝ → ℂ := (Lp.aestronglyMeasurable u).mk u
  have hHm : StronglyMeasurable H := (Lp.aestronglyMeasurable u).stronglyMeasurable_mk
  have huH : u =ᵐ[spectralKLPhysicalMeasure] H := (Lp.aestronglyMeasurable u).ae_eq_mk
  have hH : MemLp H 2 spectralKLPhysicalMeasure := (memLp_congr_ae huH).mp (Lp.memLp u)
  have hHlp : hH.toLp H = u := by
    apply Lp.ext
    exact hH.coeFn_toLp.trans huH.symm
  let U := (spectralKLPhysicalSqrtDown_memLp H hHm hH).toLp (spectralKLPhysicalSqrtDown H)
  obtain ⟨v,hv,hvε⟩ := Metric.mem_closure_iff.mp (spectralKLPositiveLebesgue_dense_smooth U) ε hε
  obtain ⟨g,hvg,hgc,hg,hgp⟩ := hv
  have hgm : MemLp g 2 spectralKLPositiveLebesgueMeasure :=
    spectral_positive_measure_memLp_compact _ g hg.continuous hgc
  have hglp : hgm.toLp g = v := by
    apply Lp.ext
    exact hgm.coeFn_toLp.trans hvg.symm
  let f := spectralKLPhysicalSqrtLift g
  have hfm : MemLp f 2 spectralKLPhysicalMeasure := spectralKLPhysicalSqrtLift_memLp g hg.continuous.measurable hgm
  have hfc : HasCompactSupport f := hgc.mul_left
  have hfp : tsupport f ⊆ Ioi (0 : ℝ) := tsupport_mul_subset_right.trans hgp
  have hcont : Continuous f := (Complex.continuous_ofReal.comp Real.continuous_sqrt).mul hg.continuous
  refine ⟨hfm.toLp f,⟨f,hfm.coeFn_toLp,hfc,hcont,hfp⟩,?_⟩
  have hnorm := spectralKLPhysicalSqrt_norm_sub H g hHm hH hg.continuous.measurable hgm
  rw [hHlp,hglp] at hnorm
  change ‖hfm.toLp f-u‖ = ‖v-U‖ at hnorm
  rw [dist_comm,dist_eq_norm,hnorm]
  simpa only [dist_eq_norm,norm_sub_rev] using hvε

end ArtinMatthews
