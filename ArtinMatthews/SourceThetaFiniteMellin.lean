module

public import ArtinMatthews.SourceSLocalExactMeasures
public import ArtinMatthews.SourceLocalMultiplicativeShell
public import Mathlib.MeasureTheory.Integral.Indicator


set_option backward.privateInPublic true
@[expose] public section

/-! The literal finite cutoff in the positive theta test. The entire
Mellin factor is its actual positive multiplicative Haar volume. -/
namespace ArtinMatthews.SourceReflection

open NumberField IsDedekindDomain MeasureTheory Set
open ArtinMatthews.SourcePhysical
open scoped NumberField ENNReal ArtinMatthews.SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

/-- A compact open finite-place theta cutoff containing one and supported at norm one. -/
structure SourceThetaFiniteCutoff where
  region : Set (P.adicCompletion K)ˣ
  isCompact : IsCompact region
  isOpen : IsOpen region
  one_mem : 1 ∈ region
  norm_eq_one : ∀ z ∈ region, ‖(z : P.adicCompletion K)‖ = 1

/-- The entire actual unit shell is one possible finite cutoff. -/
def SourceThetaFiniteCutoff.unitShell : SourceThetaFiniteCutoff K P where
  region := sourceLocalMulShell K P 0
  isCompact := sourceLocalMulShell_isCompact K P 0
  isOpen := ((sourceLocalBall_isOpen K P 0).inter
    (sourceLocalBall_isCompact K P (0 - 1)).isClosed.isOpen_compl).preimage Units.continuous_val
  one_mem := (sourceLocalMulShell_log_iff K P 0 1).mpr (by
    simp [sourceLocalValuation])
  norm_eq_one z hz := by
    simpa only [zpow_zero] using sourceLocalMulShell_norm K P 0 hz

variable {K P}

def SourceThetaFiniteCutoff.mass (U : SourceThetaFiniteCutoff K P) : ℝ :=
  (sourceLocalMulMeasure K P).real U.region

theorem SourceThetaFiniteCutoff.mass_pos (U : SourceThetaFiniteCutoff K P) : 0 < U.mass := by
  let := sourceLocalMulMeasure_isHaar K P
  rw [SourceThetaFiniteCutoff.mass, measureReal_def]
  exact ENNReal.toReal_pos (U.isOpen.measure_ne_zero _ ⟨1, U.one_mem⟩)
    U.isCompact.measure_ne_top

def SourceThetaFiniteCutoff.factor (U : SourceThetaFiniteCutoff K P) :
    (P.adicCompletion K)ˣ → ℂ :=
  U.region.indicator fun _ => 1

theorem SourceThetaFiniteCutoff.factor_integrable (U : SourceThetaFiniteCutoff K P) :
    Integrable U.factor (sourceLocalMulMeasure K P) := by
  let := sourceLocalMulMeasure_isHaar K P
  apply IntegrableOn.integrable_indicator _ U.isOpen.measurableSet
  exact integrableOn_const U.isCompact.measure_ne_top

theorem SourceThetaFiniteCutoff.factor_normWeight (U : SourceThetaFiniteCutoff K P)
    (s : ℂ) (z : (P.adicCompletion K)ˣ) :
    U.factor z * (‖(z : P.adicCompletion K)‖ : ℂ) ^ s = U.factor z := by
  by_cases hz : z ∈ U.region
  · rw [U.norm_eq_one z hz, Complex.ofReal_one, Complex.one_cpow, mul_one]
  · rw [SourceThetaFiniteCutoff.factor, indicator_of_notMem hz, zero_mul]

theorem SourceThetaFiniteCutoff.factor_integral (U : SourceThetaFiniteCutoff K P) :
    (∫ z, U.factor z ∂sourceLocalMulMeasure K P) = (U.mass : ℂ) := by
  rw [SourceThetaFiniteCutoff.factor, integral_indicator U.isOpen.measurableSet, setIntegral_const,
    Complex.real_smul, mul_one, SourceThetaFiniteCutoff.mass]

end
end ArtinMatthews.SourceReflection
