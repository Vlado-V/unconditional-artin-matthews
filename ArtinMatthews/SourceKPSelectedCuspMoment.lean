module

public import ArtinMatthews.SourceKPSelectedCuspWeight
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! The full-dimensional selected-band radial integral is entire and positive at the pole. -/

namespace ArtinMatthews
open NumberField MeasureTheory Filter Metric
open scoped NumberField MatrixGroups AdeleRing Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "HY" => sourceKPAutomorphicCompactOrbitHeight K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

def sourceKPSelectedCuspRadialValue (h : ℝ) (s : ℂ) (y : Y) : ℂ :=
  Complex.exp (((1/2 : ℂ)-s)*(Real.log (HY y/h) : ℂ))

def sourceKPSelectedCuspMoment (b : SourceKPFiniteLevelFiber K hζ) (A B h : ℝ) (s : ℂ) : ℂ :=
  ∫ y in sourceKPSelectedCuspBand K hζ b A B, sourceKPSelectedCuspRadialValue K hζ h s y ∂μY

theorem sourceKPSelectedCuspRadialValue_measurable (h : ℝ) (s : ℂ) :
    Measurable (sourceKPSelectedCuspRadialValue K hζ h s) := by
  have hH := (sourceKPAutomorphicCompactOrbitHeight_lowerSemicontinuous K hζ).measurable
  exact Complex.continuous_exp.measurable.comp
    ((Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp (hH.div_const h))).const_mul _)

theorem sourceKPSelectedCuspLog_bound (b : SourceKPFiniteLevelFiber K hζ) {A B h : ℝ}
    (hA : 1 ≤ A) (hh : 0 < h) {y : Y} (hy : y ∈ sourceKPSelectedCuspBand K hζ b A B) :
    |Real.log (HY y/h)| ≤ |Real.log (A/h)|+|Real.log (B/h)| := by
  obtain ⟨ha,hb⟩ := sourceKPSelectedCuspBand_height K hζ b hA hy
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hHpos : 0 < HY y := hApos.trans ha
  have hlow := Real.log_le_log (div_pos hApos hh) (div_le_div_of_nonneg_right ha.le hh.le)
  have hhigh := Real.log_le_log (div_pos hHpos hh) (div_le_div_of_nonneg_right hb.le hh.le)
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log (A/h)),abs_nonneg (Real.log (B/h))]
  · linarith [le_abs_self (Real.log (B/h)),abs_nonneg (Real.log (A/h))]

theorem sourceKPSelectedCuspRadialValue_norm_le (h : ℝ) (s : ℂ) (y : Y) {C : ℝ}
    (hC : |Real.log (HY y/h)| ≤ C) :
    ‖sourceKPSelectedCuspRadialValue K hζ h s y‖ ≤ Real.exp (‖(1/2 : ℂ)-s‖*C) := by
  rw [sourceKPSelectedCuspRadialValue,Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ‖((1/2 : ℂ)-s)*(Real.log (HY y/h) : ℂ)‖ := Complex.re_le_norm _
    _ ≤ _ := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]; gcongr

theorem sourceKPSelectedCuspRadialValue_integrableOn (b : SourceKPFiniteLevelFiber K hζ)
    {A B h : ℝ} (hA : 1 ≤ A) (hh : 0 < h) (s : ℂ) :
    IntegrableOn (sourceKPSelectedCuspRadialValue K hζ h s)
      (sourceKPSelectedCuspBand K hζ b A B) μY := by
  let S := sourceKPSelectedCuspBand K hζ b A B
  let : IsFiniteMeasure (Measure.restrict μY S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (sourceKPSelectedCuspBand_measure_ne_top K hζ b hA).lt_top⟩
  apply (integrable_const (Real.exp (‖(1/2 : ℂ)-s‖*(|Real.log (A/h)|+|Real.log (B/h)|)))).mono'
    (sourceKPSelectedCuspRadialValue_measurable K hζ h s).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (sourceKPSelectedCuspBand_isOpen K hζ b A B).measurableSet]
    with y hy
  exact sourceKPSelectedCuspRadialValue_norm_le K hζ h s y
    (sourceKPSelectedCuspLog_bound K hζ b hA hh hy)

theorem sourceKPSelectedCuspMoment_entire (b : SourceKPFiniteLevelFiber K hζ) {A B h : ℝ}
    (hA : 1 ≤ A) (hh : 0 < h) :
    Differentiable ℂ (sourceKPSelectedCuspMoment K hζ b A B h) := by
  intro s
  let S := sourceKPSelectedCuspBand K hζ b A B
  let μ := Measure.restrict μY S
  let : IsFiniteMeasure μ :=
    ⟨by rw [show μ Set.univ = μY S from Measure.restrict_apply_univ S];
         exact (sourceKPSelectedCuspBand_measure_ne_top K hζ b hA).lt_top⟩
  let C := |Real.log (A/h)|+|Real.log (B/h)|
  let L : Y → ℂ := fun y => (Real.log (HY y/h) : ℂ)
  let F := sourceKPSelectedCuspRadialValue K hζ h
  let F' : ℂ → Y → ℂ := fun z y => F z y * (-L y)
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hL : Measurable L :=
    Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp
      ((sourceKPAutomorphicCompactOrbitHeight_lowerSemicontinuous K hζ).measurable.div_const h))
  have hderiv (y : Y) (z : ℂ) : HasDerivAt (fun w => F w y) (F' z y) z := by
    have h := (((hasDerivAt_const z (1/2 : ℂ)).sub (hasDerivAt_id z)).mul_const (L y)).cexp
    simpa only [sourceKPSelectedCuspRadialValue,F,F',L,Pi.sub_apply,id_eq,zero_sub,neg_mul,one_mul] using h
  let D := Real.exp ((‖(1/2 : ℂ)-s‖+1)*C)*C
  have hD : Integrable (fun _ : Y => D) μ := integrable_const D
  change DifferentiableAt ℂ (fun z => ∫ y, F z y ∂μ) s
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := ball s 1) (bound := fun _ => D)
    (ball_mem_nhds s zero_lt_one) _
    (sourceKPSelectedCuspRadialValue_integrableOn K hζ b hA hh s)
    (((sourceKPSelectedCuspRadialValue_measurable K hζ h s).mul hL.neg).aestronglyMeasurable)
    _ hD _).2.differentiableAt
  · exact Eventually.of_forall (fun z =>
      (sourceKPSelectedCuspRadialValue_measurable K hζ h z).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem (sourceKPSelectedCuspBand_isOpen K hζ b A B).measurableSet]
      with y hy z hz
    have hlog : |Real.log (HY y/h)| ≤ C := sourceKPSelectedCuspLog_bound K hζ b hA hh hy
    have hzn : ‖(1/2 : ℂ)-z‖ ≤ ‖(1/2 : ℂ)-s‖+1 := by
      have hz' : ‖s-z‖ ≤ 1 := by simpa only [dist_comm,dist_eq_norm] using (show dist z s < 1 from hz).le
      rw [show (1/2 : ℂ)-z = ((1/2 : ℂ)-s)+(s-z) by ring]
      exact (norm_add_le _ _).trans (by linarith)
    change ‖F z y * (-L y)‖ ≤ D
    rw [norm_mul,norm_neg,show ‖L y‖ = |Real.log (HY y/h)| by
      rw [show L y = (Real.log (HY y/h) : ℂ) from rfl,Complex.norm_real,Real.norm_eq_abs]]
    exact mul_le_mul
      ((sourceKPSelectedCuspRadialValue_norm_le K hζ h z y hlog).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hzn hC)))
      hlog (abs_nonneg _) (Real.exp_pos _).le
  · exact Eventually.of_forall (fun y z _ => hderiv y z)

theorem sourceKPSelectedCuspMoment_analyticAt (b : SourceKPFiniteLevelFiber K hζ) {A B h : ℝ}
    (hA : 1 ≤ A) (hh : 0 < h) (s : ℂ) :
    AnalyticAt ℂ (sourceKPSelectedCuspMoment K hζ b A B h) s :=
  (sourceKPSelectedCuspMoment_entire K hζ b hA hh).analyticAt s

theorem sourceKPSelectedCuspMoment_oneSixth_re_pos (b : SourceKPFiniteLevelFiber K hζ) {A B h : ℝ}
    (hA : 1 ≤ A) (hAB : A < B) (hh : 0 < h) :
    0 < (sourceKPSelectedCuspMoment K hζ b A B h (1/6)).re := by
  let S := sourceKPSelectedCuspBand K hζ b A B
  let μ := Measure.restrict μY S
  let : NeZero μ := ⟨fun h0 => by
    have hm : μ Set.univ = 0 := by simp [h0]
    change Measure.restrict μY S Set.univ = 0 at hm
    rw [Measure.restrict_apply_univ] at hm
    exact (sourceKPSelectedCuspBand_measure_pos K hζ b hA hAB).ne' hm⟩
  have hi := sourceKPSelectedCuspRadialValue_integrableOn K hζ b (B := B) hA hh (1/6)
  have he (y : Y) : (sourceKPSelectedCuspRadialValue K hζ h (1/6) y).re =
      Real.exp (Real.log (HY y/h)/3) := by
    rw [sourceKPSelectedCuspRadialValue,show ((1/2 : ℂ)-1/6)*(Real.log (HY y/h) : ℂ) =
      ((Real.log (HY y/h)/3 : ℝ) : ℂ) by push_cast; ring,← Complex.ofReal_exp,Complex.ofReal_re]
  change 0 < (∫ y, sourceKPSelectedCuspRadialValue K hζ h (1/6) y ∂μ).re
  have hi' : Integrable (sourceKPSelectedCuspRadialValue K hζ h (1/6)) μ := hi
  have him : Integrable (fun y => Real.exp (Real.log (HY y/h)/3)) μ := by
    have hre : Integrable (fun y => (sourceKPSelectedCuspRadialValue K hζ h (1/6) y).re) μ := hi'.re
    simpa only [he] using hre
  have hr := integral_re hi
  change (∫ y, (sourceKPSelectedCuspRadialValue K hζ h (1/6) y).re ∂μ) =
    (∫ y, sourceKPSelectedCuspRadialValue K hζ h (1/6) y ∂μ).re at hr
  rw [← hr]
  simpa only [he] using integral_exp_pos him

end
end ArtinMatthews
