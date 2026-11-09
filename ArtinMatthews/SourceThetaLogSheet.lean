module

public import ArtinMatthews.SourceThetaIntegralDerivatives
public import ArtinMatthews.SourceSheetProfile


set_option backward.privateInPublic true
@[expose] public section

/-! The source03 norm sheet in the dependent log radius. The same
integrand provides the signed integral and its absolute envelope. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory Set Filter ArtinMatthews.SourcePhysical
noncomputable section

variable {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
variable (N : Y → ℝ) (G : Y → ℂ)

def sourceThetaLogSheetIntegrand (g : Circle → ℝ → ℂ) (t : ℝ) (p : Circle × Y) : ℂ :=
  g p.1 (t - Real.log (N p.2)) * G p.2

def sourceThetaLogSheet (g : Circle → ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ p, sourceThetaLogSheetIntegrand N G g t p ∂sourceCircleHaar.prod ν

def sourceThetaLogSheetAbs (g : Circle → ℝ → ℂ) (t : ℝ) : ℝ :=
  ∫ p, ‖sourceThetaLogSheetIntegrand N G g t p‖ ∂sourceCircleHaar.prod ν

variable (hNm : Measurable N) (hG : Measurable G)

include hNm hG in
theorem sourceThetaLogSheetIntegrand_measurable {g : Circle → ℝ → ℂ}
    (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (sourceThetaLogSheetIntegrand N G g)) := by
  have hθ : Measurable (fun p : ℝ × (Circle × Y) => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hy : Measurable (fun p : ℝ × (Circle × Y) => p.2.2) :=
    measurable_snd.comp measurable_snd
  exact (hg.comp (hθ.prodMk (measurable_fst.sub (Real.measurable_log.comp (hNm.comp hy))))).mul
    (hG.comp hy)

include hNm hG in
theorem sourceThetaLogSheetAbs_measurable [SFinite ν] {g : Circle → ℝ → ℂ}
    (hg : Measurable (Function.uncurry g)) : Measurable (sourceThetaLogSheetAbs ν N G g) :=
  (StronglyMeasurable.integral_prod_right'
    (sourceThetaLogSheetIntegrand_measurable N G hNm hG hg).norm.stronglyMeasurable).measurable

theorem sourceThetaLogSheetAbs_nonneg (g : Circle → ℝ → ℂ) (t : ℝ) :
    0 ≤ sourceThetaLogSheetAbs ν N G g t :=
  integral_nonneg fun _ => norm_nonneg _

theorem sourceThetaLogSheet_norm_le_abs (g : Circle → ℝ → ℂ) (t : ℝ) :
    ‖sourceThetaLogSheet ν N G g t‖ ≤ sourceThetaLogSheetAbs ν N G g t :=
  norm_integral_le_integral_norm _

include hNm hG in
/-- The genuine pointwise sheet majorant at any real weight exponent. -/
theorem sourceThetaLogSheet_weighted {g : Circle → ℝ → ℂ}
    [SFinite ν]
    (hg : Measurable (Function.uncurry g)) (hN : ∀ y, 0 < N y)
    (σ C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ θ t, ‖g θ t‖ ≤ C * Real.exp (-σ * t))
    (hI : Integrable (fun y => ‖G y‖ * (N y) ^ σ) ν) :
    (∀ t, Integrable (sourceThetaLogSheetIntegrand N G g t) (sourceCircleHaar.prod ν)) ∧
      ∃ D : ℝ, 0 ≤ D ∧ ∀ t, sourceThetaLogSheetAbs ν N G g t ≤ D * Real.exp (-σ * t) := by
  let W (p : Circle × Y) := ‖G p.2‖ * (N p.2) ^ σ
  have hW : Integrable W (sourceCircleHaar.prod ν) := hI.comp_snd sourceCircleHaar
  have hW₀ (p : Circle × Y) : 0 ≤ W p :=
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hN _).le _)
  have hBound (t : ℝ) (p : Circle × Y) :
      ‖sourceThetaLogSheetIntegrand N G g t p‖ ≤ (C * Real.exp (-σ * t)) * W p := by
    rw [sourceThetaLogSheetIntegrand, norm_mul]
    calc
      _ ≤ (C * Real.exp (-σ * (t - Real.log (N p.2)))) * ‖G p.2‖ :=
        mul_le_mul_of_nonneg_right (hb _ _) (norm_nonneg _)
      _ = _ := by
        dsimp only [W]
        rw [show -σ * (t - Real.log (N p.2)) = -σ * t + Real.log (N p.2) * σ by ring,
          Real.exp_add, Real.rpow_def_of_pos (hN _)]
        ac_rfl
  have hF (t : ℝ) : Integrable (sourceThetaLogSheetIntegrand N G g t) (sourceCircleHaar.prod ν) :=
    (hW.const_mul (C * Real.exp (-σ * t))).mono'
      ((sourceThetaLogSheetIntegrand_measurable N G hNm hG hg).comp
        measurable_prodMk_left).aestronglyMeasurable (Eventually.of_forall (hBound t))
  refine ⟨hF, C * (∫ p, W p ∂sourceCircleHaar.prod ν),
    mul_nonneg hC (integral_nonneg hW₀), fun t => ?_⟩
  calc
    _ ≤ ∫ p, (C * Real.exp (-σ * t)) * W p ∂sourceCircleHaar.prod ν :=
      integral_mono (hF t).norm (hW.const_mul _) (hBound t)
    _ = _ := by rw [integral_const_mul]; ac_rfl

include hNm hG in
/-- Only the chosen complex log radius is differentiated. The other
coordinates and their measure stay fixed. -/
theorem sourceThetaLogSheet_hasDerivAt {g g' : Circle → ℝ → ℂ}
    [SFinite ν]
    (hg : Measurable (Function.uncurry g)) (hg' : Measurable (Function.uncurry g'))
    (hd : ∀ θ t, HasDerivAt (g θ) (g' θ t) t) (hN : ∀ y, 0 < N y)
    (C C' : ℝ) (hC : 0 ≤ C) (hb : ∀ θ t, ‖g θ t‖ ≤ C)
    (hb' : ∀ θ t, ‖g' θ t‖ ≤ C') (hI : Integrable (fun y => ‖G y‖) ν) (t : ℝ) :
    HasDerivAt (sourceThetaLogSheet ν N G g) (sourceThetaLogSheet ν N G g' t) t := by
  have hF := (sourceThetaLogSheet_weighted ν N G hNm hG hg hN 0 C hC
    (fun θ u => by simpa using hb θ u) (by simpa using hI)).1
  have hF' (x : ℝ) : AEStronglyMeasurable (sourceThetaLogSheetIntegrand N G g' x)
      (sourceCircleHaar.prod ν) :=
    Measurable.aestronglyMeasurable
      ((sourceThetaLogSheetIntegrand_measurable N G hNm hG hg').comp measurable_prodMk_left)
  refine sourceThetaIntegral_hasDerivAt (sourceCircleHaar.prod ν)
    (sourceThetaLogSheetIntegrand N G g) (sourceThetaLogSheetIntegrand N G g') hF hF'
    (fun x p => ?_) (fun p => C' * ‖G p.2‖) ((hI.comp_snd sourceCircleHaar).const_mul _)
    (fun x p => ?_) t
  · let f (u : ℝ) := u - Real.log (N p.2)
    have hf : HasDerivAt f 1 x := (hasDerivAt_id x).sub_const (Real.log (N p.2))
    simpa only [sourceThetaLogSheetIntegrand, Function.comp_def, f, one_smul] using
      (((hd p.1 (f x)).scomp x hf).mul_const (G p.2))
  · rw [sourceThetaLogSheetIntegrand, norm_mul]
    exact mul_le_mul_of_nonneg_right (hb' _ _) (norm_nonneg _)

end
end ArtinMatthews.SourceReflection
