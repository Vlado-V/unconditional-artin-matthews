module

public import ArtinMatthews.SourceLocalMultiplicativeShell
public import ArtinMatthews.SourceLocalMultiplicativeHaar
public import ArtinMatthews.StandardLocalBall
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


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
