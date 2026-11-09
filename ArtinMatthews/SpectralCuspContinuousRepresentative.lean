module

public import ArtinMatthews.SpectralCuspConstantTermRepresentative


set_option backward.privateInPublic true
@[expose] public section

/-! Literal normalized horizontal means of continuous representatives of
actual cusp L2 vectors, with a continuous extension below the tail. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace ArtinMatthews

def cuspContinuousPlaneExtension (Y : ℝ) (hY : 0<Y) (F : UpperHalfPlane → ℂ)
    (p : ℝ×ℝ) : ℂ :=
  F ⟨Complex.mk p.1 (max (Y/2) p.2),lt_of_lt_of_le (half_pos hY) (le_max_left _ _)⟩

theorem cuspContinuousPlaneExtension_continuous (Y : ℝ) (hY : 0<Y)
    (F : UpperHalfPlane → ℂ) (hF : Continuous F) :
    Continuous (cuspContinuousPlaneExtension Y hY F) := by
  apply hF.comp
  apply Continuous.upperHalfPlaneMk
  have hc := Complex.equivRealProdCLM.symm.continuous.comp
    (continuous_fst.prodMk (continuous_const.max continuous_snd) :
      Continuous (fun p : ℝ×ℝ => (p.1,max (Y/2) p.2)))
  convert hc using 1
  funext p
  exact (Complex.equivRealProdCLM.symm_apply_apply (Complex.mk p.1 (max (Y/2) p.2))).symm

theorem cuspContinuousPlaneExtension_at_upper (Y : ℝ) (hY : 0<Y)
    (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) (hz : Y≤z.im) :
    cuspContinuousPlaneExtension Y hY F (z.re,z.im)=F z := by
  unfold cuspContinuousPlaneExtension
  congr 1
  apply UpperHalfPlane.ext
  apply Complex.ext
  · rfl
  · change max (Y/2) z.im=z.im
    exact max_eq_right (by linarith)

theorem cuspHyperbolicConstantTerm_continuous_representative (w Y : ℝ)
    (hw : 0<w) (hY : 0<Y) (U : CuspHyperbolicL2 w Y)
    (F : UpperHalfPlane → ℂ) (hF : Continuous F)
    (hUF : U =ᵐ[volume.restrict (hyperbolicCuspStrip w Y)] F) :
    cuspHyperbolicConstantTerm w Y hY U =ᵐ[cuspVerticalMeasure Y]
      cuspHorizontalMean w (cuspContinuousPlaneExtension Y hY F) := by
  let G := cuspContinuousPlaneExtension Y hY F
  have hG : Continuous G := cuspContinuousPlaneExtension_continuous Y hY F hF
  have he : U =ᵐ[volume.restrict (hyperbolicCuspStrip w Y)]
      fun z : UpperHalfPlane => G (z.re,z.im) := by
    filter_upwards [hUF,ae_restrict_mem
      ((measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
        (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable))] with z hz hzS
    exact hz.trans (cuspContinuousPlaneExtension_at_upper Y hY F z hzS.2.le).symm
  have hh := (memLp_congr_ae he).mp (Lp.memLp U)
  have hLp : hh.toLp (fun z : UpperHalfPlane => G (z.re,z.im))=U := by
    apply Lp.ext
    exact hh.coeFn_toLp.trans he.symm
  rw [← hLp]
  exact cuspHyperbolicConstantTerm_ae_representative w Y hw hY G hG hh

end ArtinMatthews
