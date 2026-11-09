module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.Set


set_option backward.privateInPublic true
@[expose] public section

/-! Literal measurable cutoffs in complex L2 and their exact tail norms. -/
namespace ArtinMatthews
open MeasureTheory Set
open scoped ENNReal Topology
noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

abbrev HeightL2 := Lp ℂ 2 μ

def measurableL2CutoffValue (S : Set X) (hS : MeasurableSet S) (f : HeightL2 μ) : HeightL2 μ :=
  ((Lp.memLp f).indicator hS.nullMeasurableSet).toLp (S.indicator f)

theorem measurableL2CutoffValue_coe (S : Set X) (hS : MeasurableSet S) (f : HeightL2 μ) :
    measurableL2CutoffValue μ S hS f =ᵐ[μ] S.indicator f :=
  MemLp.coeFn_toLp _

theorem measurableL2CutoffValue_norm_le (S : Set X) (hS : MeasurableSet S) (f : HeightL2 μ) :
    ‖measurableL2CutoffValue μ S hS f‖ ≤ ‖f‖ := by
  rw [measurableL2CutoffValue, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_indicator_le f hS.nullMeasurableSet)

def measurableL2Cutoff (S : Set X) (hS : MeasurableSet S) : HeightL2 μ →L[ℂ] HeightL2 μ :=
  LinearMap.mkContinuous
    { toFun := measurableL2CutoffValue μ S hS
      map_add' f g := by
        apply Lp.ext
        filter_upwards [measurableL2CutoffValue_coe μ S hS (f + g),
          measurableL2CutoffValue_coe μ S hS f, measurableL2CutoffValue_coe μ S hS g,
          Lp.coeFn_add f g, Lp.coeFn_add (measurableL2CutoffValue μ S hS f)
            (measurableL2CutoffValue μ S hS g)] with x hfg hf hg ha hb
        rw [hfg, hb]
        simp only [Pi.add_apply]
        rw [hf, hg]
        by_cases hx : x ∈ S
        · simpa only [Set.indicator_of_mem hx, Pi.add_apply] using ha
        · simp only [Set.indicator_of_notMem hx, add_zero]
      map_smul' c f := by
        apply Lp.ext
        filter_upwards [measurableL2CutoffValue_coe μ S hS (c • f),
          measurableL2CutoffValue_coe μ S hS f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (measurableL2CutoffValue μ S hS f)] with x hcf hf ha hb
        change (measurableL2CutoffValue μ S hS (c • f)) x = (c • measurableL2CutoffValue μ S hS f) x
        rw [hcf, hb]
        simp only [Pi.smul_apply]
        rw [hf]
        by_cases hx : x ∈ S
        · simpa only [Set.indicator_of_mem hx, Pi.smul_apply] using ha
        · simp only [Set.indicator_of_notMem hx, smul_zero] }
    1 (fun f => by simpa using measurableL2CutoffValue_norm_le μ S hS f)

theorem measurableL2Cutoff_coe (S : Set X) (hS : MeasurableSet S) (f : HeightL2 μ) :
    measurableL2Cutoff μ S hS f =ᵐ[μ] S.indicator f :=
  measurableL2CutoffValue_coe μ S hS f

theorem measurableL2Cutoff_sub (S : Set X) (hS : MeasurableSet S) (f : HeightL2 μ) :
    f - measurableL2Cutoff μ S hS f = measurableL2Cutoff μ Sᶜ hS.compl f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub f (measurableL2Cutoff μ S hS f),
    measurableL2Cutoff_coe μ S hS f, measurableL2Cutoff_coe μ Sᶜ hS.compl f] with x hsub hSx hScx
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hSx, hScx]
  by_cases hx : x ∈ S <;> simp [hx]

theorem heightL2_norm_sq_integral (f : HeightL2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) f, L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  simp only [inner_self_eq_norm_sq]

theorem measurableL2Cutoff_norm_sq (S : Set X) (hS : MeasurableSet S) (f : HeightL2 μ) :
    ‖measurableL2Cutoff μ S hS f‖ ^ 2 = ∫ x in S, ‖f x‖ ^ 2 ∂μ := by
  rw [heightL2_norm_sq_integral μ]
  calc
    _ = ∫ x, S.indicator (fun y => ‖f y‖ ^ 2) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [measurableL2Cutoff_coe μ S hS f] with x hx
      rw [hx]
      by_cases h : x ∈ S <;> simp [h]
    _ = _ := integral_indicator hS

theorem measurableL2Cutoff_tail_norm_sq (S : Set X) (hS : MeasurableSet S) (f : HeightL2 μ) :
    ‖f - measurableL2Cutoff μ S hS f‖ ^ 2 = ∫ x in Sᶜ, ‖f x‖ ^ 2 ∂μ := by
  rw [measurableL2Cutoff_sub, measurableL2Cutoff_norm_sq]

def l2HeightCutoff (H : X → ℝ) (hH : Measurable H) (T : ℝ) : HeightL2 μ →L[ℂ] HeightL2 μ :=
  measurableL2Cutoff μ {x | H x ≤ T} (measurableSet_le hH measurable_const)

theorem l2HeightCutoff_coe (H : X → ℝ) (hH : Measurable H) (T : ℝ) (f : HeightL2 μ) :
    l2HeightCutoff μ H hH T f =ᵐ[μ] {x | H x ≤ T}.indicator f :=
  measurableL2Cutoff_coe μ _ _ f

theorem l2HeightCutoff_norm_le (H : X → ℝ) (hH : Measurable H) (T : ℝ) (f : HeightL2 μ) :
    ‖l2HeightCutoff μ H hH T f‖ ≤ ‖f‖ :=
  measurableL2CutoffValue_norm_le μ {x | H x ≤ T} (measurableSet_le hH measurable_const) f

theorem l2HeightCutoff_norm_sq (H : X → ℝ) (hH : Measurable H) (T : ℝ) (f : HeightL2 μ) :
    ‖l2HeightCutoff μ H hH T f‖ ^ 2 = ∫ x in {x | H x ≤ T}, ‖f x‖ ^ 2 ∂μ :=
  measurableL2Cutoff_norm_sq μ _ _ f

theorem l2HeightCutoff_tail_norm_sq (H : X → ℝ) (hH : Measurable H) (T : ℝ) (f : HeightL2 μ) :
    ‖f - l2HeightCutoff μ H hH T f‖ ^ 2 = ∫ x in {x | T < H x}, ‖f x‖ ^ 2 ∂μ := by
  rw [l2HeightCutoff, measurableL2Cutoff_tail_norm_sq]
  simp only [Set.compl_ofPred, not_le]

end
end ArtinMatthews
