module

public import ArtinMatthews.SourceKPCuspFourierMomentParameter
public import ArtinMatthews.SourceKPArchJacquetFrequencyPositivity


set_option backward.privateInPublic true
@[expose] public section

/-! The same compact full-dimensional height box has a nonzero actual
archimedean Fourier moment for every nonzero rational frequency. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCuspArchFourierMoment_oneSixth_re_pos (m : Kˣ) :
    0 < (sourceKPCuspArchFourierMoment K hζ m (sourceKPCuspHeightBox K) (1/6)).re := by
  let S := sourceKPCuspHeightBox K
  let μ := (sourceKPCuspProductHeightMeasure K).restrict S
  let F := sourceKPTraceJacquetArchProfile K hζ m (1/6)
  have hi : Integrable F μ := sourceKPCuspArchFourierProfile_integrableOn
    K hζ (1 : 𝓞 K) one_ne_zero m (s := (1/6:ℂ)) (by norm_num)
    S (sourceKPCuspHeightBox_isCompact K) (sourceKPCuspHeightBox_positive K)
  have hp : ∀ᵐ y ∂μ, 0 < (F y).re := by
    filter_upwards [ae_restrict_mem (sourceKPCuspHeightBox_isCompact K).measurableSet] with y hy
    exact (sourceKPTraceJacquetArchProfile_oneSixth_positive K hζ m y
      (sourceKPCuspHeightBox_positive K y hy)).1
  have he : Function.support (fun y => (F y).re) =ᵐ[μ] Set.univ := by
    filter_upwards [hp] with y hy
    exact propext (by simp only [Function.mem_support,Set.mem_univ,iff_true]; exact hy.ne')
  have hmass : 0 < μ (Function.support (fun y => (F y).re)) := by
    rw [measure_congr he]
    change 0 < ((sourceKPCuspProductHeightMeasure K).restrict S) Set.univ
    rw [Measure.restrict_apply_univ]
    exact (sourceKPCuspHeightBox_mass K).1
  have hpos := (integral_pos_iff_support_of_nonneg_ae (hp.mono fun _ h => h.le) hi.re).mpr hmass
  have hr := integral_re hi
  change (∫ y, (F y).re ∂μ) = (∫ y, F y ∂μ).re at hr
  rw [hr] at hpos
  exact hpos

theorem sourceKPCuspArchFourierMoment_oneSixth_ne_zero (m : Kˣ) :
    sourceKPCuspArchFourierMoment K hζ m (sourceKPCuspHeightBox K) (1/6) ≠ 0 := by
  intro h
  have hp := sourceKPCuspArchFourierMoment_oneSixth_re_pos K hζ m
  rw [h,Complex.zero_re] at hp
  exact (lt_irrefl _ hp)

end
end ArtinMatthews
