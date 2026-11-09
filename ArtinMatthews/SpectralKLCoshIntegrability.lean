module

public import ArtinMatthews.SpectralKLPhysicalCompactData
public import Mathlib.Analysis.Complex.Trigonometric


set_option backward.privateInPublic true
@[expose] public section

/-! An actual L1 criterion for cosh-corrected data in the literal KL
spectral measure. -/

noncomputable section
open Set MeasureTheory
namespace ArtinMatthews

theorem spectralKLCosh_integrable (H : ℝ → ℂ) (G : ℝ → ℝ)
    (hH : Measurable H)
    (hG0 : ∀ t : ℝ, 0 < t → 0 ≤ G t)
    (hI : IntegrableOn (fun t => t*G t) (Ioi (0 : ℝ)))
    (hbound : ∀ t : ℝ, 0 < t → ‖H t‖ ≤ G t/Real.cosh (Real.pi*t)) :
    Integrable H spectralKLSpectralMeasure := by
  apply (integrable_norm_iff hH.aestronglyMeasurable).mp
  apply (spectralKLPositiveWeightMeasure_integrable_iff spectralKLPlancherelWeight (fun t => ‖H t‖)
    spectralKLPlancherelWeight_continuous.measurable
    (fun t ht => (spectralKLPlancherelWeight_pos ht).le)).mpr
  have hi := hI.const_mul (2/Real.pi^2)
  apply hi.mono'
    ((spectralKLPlancherelWeight_continuous.measurable.mul hH.norm).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hw : 0 ≤ spectralKLPlancherelWeight t := (spectralKLPlancherelWeight_pos ht).le
  have ht0 : 0 < t := ht
  have hGt := hG0 t ht
  have hC : 0 ≤ 2/Real.pi^2*t*G t := by positivity
  change ‖spectralKLPlancherelWeight t*‖H t‖‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg hw (norm_nonneg _))]
  calc
    _ ≤ spectralKLPlancherelWeight t*(G t/Real.cosh (Real.pi*t)) :=
      mul_le_mul_of_nonneg_left (hbound t ht) hw
    _ = (2/Real.pi^2*t*G t)*(Real.sinh (Real.pi*t)/Real.cosh (Real.pi*t)) := by
      unfold spectralKLPlancherelWeight
      ring
    _ ≤ 2/Real.pi^2*t*G t :=
      mul_le_of_le_one_right hC ((div_le_one (Real.cosh_pos _)).mpr (Real.sinh_lt_cosh _).le)
    _ = _ := by ring

end ArtinMatthews
