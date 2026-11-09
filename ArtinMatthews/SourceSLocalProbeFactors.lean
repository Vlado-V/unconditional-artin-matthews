module

public import ArtinMatthews.SourceSLocalWholeMellin
public import ArtinMatthews.SourceSLocalOtherMellin
public import ArtinMatthews.SourceLocalAnnularMellin


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory Filter
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical SchwartzMap
noncomputable section

def sourceProbeArchFourier : 𝓢(ℂ, ℂ) :=
  sourceComplexTraceFourierSchwartz sourceAnnularSchwartzTest

theorem sourceProbeArchFourier_apply (z : ℂ) :
    sourceProbeArchFourier z = sourceComplexTraceFourier sourceAnnularSchwartzTest z :=
  sourceComplexTraceFourierSchwartz_apply _ _

theorem sourceProbeArchMellin_sixth_ne_zero :
    sourceComplexMellin sourceProbeArchFourier (1 / 6 : ℂ) ≠ 0 := by
  have he : (1 / 6 : ℂ) = ((1 / 6 : ℝ) : ℂ) := by norm_num
  rw [he, sourceComplexMellin_real_eq]
  norm_num [show (2 : ℝ) * (1 / 6) - 2 = -(5 / 3) by norm_num, sourceProbeArchFourier_apply]
  exact sourceAnnularSchwartzTest_trace_mellin_nonzero

variable (K : Type) [Field K] [NumberField K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

def sourceProbeArchFactor (w : InfinitePlace K) (u : w.Completionˣ) : ℂ :=
  sourceProbeArchFourier (sourceComplexPlaceUnitsEquiv (sourceSLocalComplexPlace K hζ w) u : ℂ)

def sourceProbeFiniteFactor (p : S) (u : (p.val.adicCompletion K)ˣ) : ℂ :=
  sourceLocalFourier K p.val (sourceLocalUnitTest K p.val) u

theorem sourceProbeArchFactor_measurable (w : InfinitePlace K) :
    Measurable (sourceProbeArchFactor K hζ w) :=
  sourceProbeArchFourier.continuous.measurable.comp (Units.continuous_val.measurable.comp
    (sourceComplexPlaceUnitsEquiv (sourceSLocalComplexPlace K hζ w)).continuous.measurable)

theorem sourceProbeFiniteFactor_measurable (p : S) :
    Measurable (sourceProbeFiniteFactor K S p) := by
  let P := p.val
  have h (n : ℤ) : Measurable (fun u : (P.adicCompletion K)ˣ => sourceLocalBallIndicator K P n u) :=
    (sourceLocalBallIndicator_locallyConstant K P n).continuous.measurable.comp Units.continuous_val.measurable
  have hEq : sourceProbeFiniteFactor K S p = fun u : (P.adicCompletion K)ˣ =>
      ((sourceLocalSelfDual K P).real (sourceLocalBall K P 0) : ℂ) *
        sourceLocalBallIndicator K P (sourceDifferentExponent K P : ℤ) u -
      ((sourceLocalSelfDual K P).real (sourceLocalBall K P (-1)) : ℂ) *
        sourceLocalBallIndicator K P ((sourceDifferentExponent K P : ℤ) + 1) u :=
    funext (fun u => sourceLocalUnitTestFourier_raw K P u)
  rw [hEq]
  exact ((h _).const_mul _).sub ((h _).const_mul _)

theorem sourceProbeArchFactor_weighted_norm_integrable (w : InfinitePlace K) (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun z => ‖sourceProbeArchFactor K hζ w z‖ * (sourceSheetArchNorm w z) ^ σ)
      (sourceSLocalArchUnitMeasure K hζ w) := by
  let hw := sourceSLocalComplexPlace K hζ w
  have h := (sourceComplexPlaceUnitMellinIntegrand_integrable hw sourceProbeArchFourier
    (σ : ℂ) hσ).norm
  apply h.congr
  filter_upwards with z
  rw [sourceComplexUnitMellinIntegrand_norm, Complex.ofReal_re, sourceProbeArchFactor,
    sourceSheetArchNorm_eq_complex hw, sourceComplexPlaceUnitsEquiv_val]

theorem sourceProbeFiniteFactor_weighted_norm_integrable (p : S) (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun z => ‖sourceProbeFiniteFactor K S p z‖ * (sourceSheetFiniteNorm S p z) ^ σ)
      (sourceSLocalFiniteUnitMeasure K S p) := by
  have h := (sourceLocalAnnularMellin_integrable K p.val (σ : ℂ) hσ).norm
  apply h.congr
  filter_upwards with z
  rw [sourceLocalAnnularMellinIntegrand, sourceLocalMellinWeight, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr z.ne_zero), Complex.ofReal_re]
  rfl

theorem sourceProbeArchFactor_mellin_eq (w : InfinitePlace K) (s : ℂ) :
    (∫ z, sourceProbeArchFactor K hζ w z * (sourceSheetArchNorm w z : ℂ) ^ s
      ∂sourceSLocalArchUnitMeasure K hζ w) = sourceComplexMellin sourceProbeArchFourier s := by
  let hw := sourceSLocalComplexPlace K hζ w
  calc
    _ = ∫ z : w.Completionˣ, sourceComplexUnitMellinIntegrand sourceProbeArchFourier s
        (sourceComplexPlaceUnitsEquiv hw z) ∂sourceComplexPlaceUnitHaar hw := by
      apply integral_congr_ae
      filter_upwards with z
      rw [sourceProbeArchFactor, sourceComplexUnitMellinIntegrand,
        sourceSheetArchNorm_eq_complex hw, sourceComplexPlaceUnitsEquiv_val]
    _ = _ := sourceComplexPlaceUnitHaar_mellin_eq hw _ _

theorem sourceProbeFiniteFactor_mellin_eq (p : S) (s : ℂ) :
    (∫ z, sourceProbeFiniteFactor K S p z * (sourceSheetFiniteNorm S p z : ℂ) ^ s
      ∂sourceSLocalFiniteUnitMeasure K S p) = sourceLocalAnnularMellin K p.val s := rfl

end
end ArtinMatthews.SourcePhysical
