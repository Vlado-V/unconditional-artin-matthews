module

public import ArtinMatthews.MarkedMajorOscillatoryDerivatives
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace


set_option backward.privateInPublic true
@[expose] public section

/-! The actual modulated cutoff, its compact logarithmic profile, and its
normalized one-dimensional Fourier coefficient. -/
namespace ArtinMatthews
open MeasureTheory Set Complex
open scoped ContDiff FourierTransform SchwartzMap
noncomputable section

def markedMellinIsolatedCutoff (η : ℝ → ℂ) (θ : ℝ) : ℝ → ℂ :=
  markedOscillatoryFamily η (fun y => -(2*Real.pi)*y) θ

def markedMellinIsolationLogProfile (η : ℝ → ℂ) (θ : ℝ) : ℝ → ℂ :=
  markedOscillatoryFamily (fun z => η (Real.exp z)) (fun z => -(2*Real.pi)*Real.exp z) θ

theorem markedMellinIsolationLogProfile_eq (η : ℝ → ℂ) (θ z : ℝ) :
    markedMellinIsolationLogProfile η θ z = markedMellinIsolatedCutoff η θ (Real.exp z) := rfl

theorem markedMellinIsolatedCutoff_eq (η : ℝ → ℂ) (θ y : ℝ) :
    markedMellinIsolatedCutoff η θ y =
      η y * Complex.exp (-(2*(Real.pi : ℂ)*I*(θ : ℂ)*(y : ℂ))) := by
  unfold markedMellinIsolatedCutoff markedOscillatoryFamily markedOscillatoryPhase markedRealOscillator
  congr 2
  push_cast
  ring

theorem markedMellinIsolationLogProfile_contDiff (η : ℝ → ℂ)
    (hη : ContDiff ℝ ∞ η) (θ : ℝ) : ContDiff ℝ ∞ (markedMellinIsolationLogProfile η θ) := by
  exact markedOscillatoryFamily_contDiff _ _ (hη.comp Real.contDiff_exp) (by fun_prop) θ

theorem markedMellinIsolationLogProfile_tsupport (η : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support η ⊆ Icc a b) (θ : ℝ) :
    tsupport (markedMellinIsolationLogProfile η θ) ⊆ Icc (Real.log a) (Real.log b) := by
  apply closure_minimal _ isClosed_Icc
  intro z hz
  have hη : η (Real.exp z) ≠ 0 := by
    intro h
    apply hz
    simp [markedMellinIsolationLogProfile,markedOscillatoryFamily,h]
  have h := hsupp hη
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log ha h.1
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) h.2

theorem markedMellinIsolationLogProfile_hasCompactSupport (η : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support η ⊆ Icc a b) (θ : ℝ) :
    HasCompactSupport (markedMellinIsolationLogProfile η θ) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (markedMellinIsolationLogProfile_tsupport η ha hsupp θ)

def markedMellinIsolationSchwartz (η : ℝ → ℂ) (hη : ContDiff ℝ ∞ η)
    {a b : ℝ} (ha : 0 < a) (hsupp : Function.support η ⊆ Icc a b) (θ : ℝ) : SchwartzMap ℝ ℂ :=
  (markedMellinIsolationLogProfile_hasCompactSupport η ha hsupp θ).toSchwartzMap
    (markedMellinIsolationLogProfile_contDiff η hη θ)

def markedMellinIsolationFrequencyScale : ℝ ≃L[ℝ] ℝ :=
  (LinearEquiv.smulOfNeZero ℝ ℝ (2*Real.pi)⁻¹
    (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))).toContinuousLinearEquiv

/-- The actual coefficient for inversion with exp(i*xi*log y). -/
def markedMellinIsolationCoefficient (η : ℝ → ℂ) (hη : ContDiff ℝ ∞ η)
    {a b : ℝ} (ha : 0 < a) (hsupp : Function.support η ⊆ Icc a b) (θ : ℝ) : SchwartzMap ℝ ℂ :=
  ((2*Real.pi)⁻¹ : ℝ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ markedMellinIsolationFrequencyScale
    (𝓕 (markedMellinIsolationSchwartz η hη ha hsupp θ))

theorem markedMellinIsolationCoefficient_apply (η : ℝ → ℂ) (hη : ContDiff ℝ ∞ η)
    {a b : ℝ} (ha : 0 < a) (hsupp : Function.support η ⊆ Icc a b) (θ ξ : ℝ) :
    markedMellinIsolationCoefficient η hη ha hsupp θ ξ =
      (((2*Real.pi)⁻¹ : ℝ) : ℂ)*(𝓕 (markedMellinIsolationSchwartz η hη ha hsupp θ)) (ξ/(2*Real.pi)) := by
  change (((2*Real.pi)⁻¹ : ℝ) • (𝓕 (markedMellinIsolationSchwartz η hη ha hsupp θ))
    ((2*Real.pi)⁻¹*ξ)) = _
  rw [Complex.real_smul]
  congr 2
  ring

end
end ArtinMatthews
