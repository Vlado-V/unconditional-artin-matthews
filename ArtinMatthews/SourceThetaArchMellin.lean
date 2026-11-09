module

public import ArtinMatthews.SourceThetaBesselMellin
public import ArtinMatthews.SourceSLocalProbeSheetIdentity
public import ArtinMatthews.SourceLogMellinCoordinate


set_option backward.privateInPublic true
@[expose] public section

/-! The positive theta Mellin integral in the actual local trace Haar
normalization. The angle mass is exactly two pi. -/
namespace ArtinMatthews.SourceReflection

open NumberField NumberField.InfinitePlace MeasureTheory Set
open ArtinMatthews.SourcePhysical
open scoped NumberField Classical ENNReal ArtinMatthews.SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (v : InfinitePlace K)

local notation "hv" => sourceSLocalComplexPlace K hζ v
local notation "μ" => sourceSLocalArchUnitMeasure K hζ v

def sourceThetaArchFactor (c : ℝ) (z : v.Completionˣ) : ℂ :=
  sourceThetaBesselProfile c (sourceSheetArchNorm v z)

def sourceThetaArchMellinIntegrand (c : ℝ) (s : ℂ) (z : v.Completionˣ) : ℂ :=
  sourceThetaArchFactor K v c z * (sourceSheetArchNorm v z : ℂ) ^ s

private def sourceThetaArchPolarEquiv : Circle × Multiplicative ℝ ≃ᵐ v.Completionˣ :=
  (sourceComplexUnitPolarHomeomorph.trans
    (sourceComplexPlaceUnitsEquiv hv).symm.toHomeomorph).toMeasurableEquiv

private theorem sourceThetaArchPolarEquiv_measurePreserving :
    MeasurePreserving (sourceThetaArchPolarEquiv K hζ v)
      (sourceCircleHaar.prod sourceRealLogHaar) μ :=
  ⟨(sourceThetaArchPolarEquiv K hζ v).measurable,
    (sourceSLocalArchUnitMeasure_eq_polar K hζ v).symm⟩

private theorem sourceThetaArchNorm_polar (p : Circle × Multiplicative ℝ) :
    sourceSheetArchNorm v (sourceThetaArchPolarEquiv K hζ v p) = Real.exp p.2.toAdd := by
  rw [sourceSheetArchNorm_eq_complex hv]
  change ‖((sourceComplexPlaceUnitsEquiv hv
    ((sourceComplexPlaceUnitsEquiv hv).symm (sourceComplexUnitPolarMulEquiv p)) : ℂˣ) : ℂ)‖ ^ 2 = _
  rw [ContinuousMulEquiv.apply_symm_apply]
  change ‖((sourceComplexRadialUnit p.2.toAdd * Circle.toUnits p.1 : ℂˣ) : ℂ)‖ ^ 2 = _
  rw [sourceComplexRadialUnit_mul_angle_norm, pow_two, ← Real.exp_add]
  congr 1
  ring

private theorem sourceThetaArchMellinIntegrand_polar (c : ℝ) (s : ℂ) (p : Circle × Multiplicative ℝ) :
    sourceThetaArchMellinIntegrand K v c s (sourceThetaArchPolarEquiv K hζ v p) =
      Complex.exp (s * (p.2.toAdd : ℂ)) * sourceThetaBesselProfile c (Real.exp p.2.toAdd) := by
  rw [sourceThetaArchMellinIntegrand, sourceThetaArchFactor, sourceThetaArchNorm_polar K hζ v,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, mul_comm (p.2.toAdd : ℂ) s, mul_comm]

theorem sourceThetaArchMellinIntegrand_integrable {c : ℝ} (hc : 0 < c) (s : ℂ)
    (hs : -(5 / 6 : ℝ) < s.re) :
    Integrable (sourceThetaArchMellinIntegrand K v c s) μ := by
  have : IsFiniteMeasure sourceCircleHaar :=
    ⟨by rw [sourceCircleHaar_univ]; exact ENNReal.ofReal_lt_top⟩
  have h := (sourceMellinConvergent_iff_log _ _).mp (sourceThetaBesselProfile_mellinConvergent hc s hs)
  let e := sourceThetaArchPolarEquiv K hζ v
  have hp := sourceThetaArchPolarEquiv_measurePreserving K hζ v
  refine (hp.integrable_comp_emb e.measurableEmbedding).mp ?_
  exact (h.comp_snd sourceCircleHaar).congr (Filter.Eventually.of_forall fun p =>
    (sourceThetaArchMellinIntegrand_polar K hζ v c s p).symm)

theorem sourceThetaArchMellinIntegrand_integral {c : ℝ} (hc : 0 < c) (s : ℂ)
    (hs : -(5 / 6 : ℝ) < s.re) :
    (∫ z, sourceThetaArchMellinIntegrand K v c s z ∂μ) =
      ((2 * Real.pi : ℝ) : ℂ) *
        ((2 : ℂ) ^ (2 * s + 1) * (c : ℂ) ^ (-2 * s - 2) *
          Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) := by
  let A (t : Multiplicative ℝ) :=
    Complex.exp (s * (t.toAdd : ℂ)) * sourceThetaBesselProfile c (Real.exp t.toAdd)
  have hAngle : (∫ _ : Circle, (1 : ℂ) ∂sourceCircleHaar) = ((2 * Real.pi : ℝ) : ℂ) := by
    rw [integral_const, measureReal_def, sourceCircleHaar_univ,
      ENNReal.toReal_ofReal (by positivity), Complex.real_smul, mul_one]
  have hA : (∫ t, A t ∂sourceRealLogHaar) = mellin (sourceThetaBesselProfile c) s :=
    (sourceMellin_eq_log (sourceThetaBesselProfile c) s).symm
  calc
    _ = ∫ p : Circle × Multiplicative ℝ, sourceThetaArchMellinIntegrand K v c s
        (sourceThetaArchPolarEquiv K hζ v p) ∂sourceCircleHaar.prod sourceRealLogHaar :=
      ((sourceThetaArchPolarEquiv_measurePreserving K hζ v).integral_comp'
        (sourceThetaArchMellinIntegrand K v c s)).symm
    _ = ∫ p : Circle × Multiplicative ℝ, (1 : ℂ) * A p.2
        ∂sourceCircleHaar.prod sourceRealLogHaar := by
      apply integral_congr_ae
      filter_upwards with p
      rw [one_mul, sourceThetaArchMellinIntegrand_polar K hζ v]
    _ = _ := by
      rw [integral_prod_mul (fun _ : Circle => (1 : ℂ)) A, hAngle, hA,
        sourceThetaBesselProfile_mellin hc s hs]

end
end ArtinMatthews.SourceReflection
