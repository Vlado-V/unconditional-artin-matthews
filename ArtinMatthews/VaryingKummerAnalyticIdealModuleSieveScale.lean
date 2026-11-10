module

public import ArtinMatthews.VaryingKummerAnalyticIdealModuleAdditiveSieve
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact norm-cutoff dependence in the fixed-ideal Gaussian sieve.
The constants below retain their dependence on the number field and ideal. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem idealModuleCoordinateSeparationRadius_pow (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {U : ℝ} (hU : 0 < U) :
    (idealModuleCoordinateSeparationRadius K I hI U)^(Module.finrank ℚ K) =
      (1/(|(NumberField.discr K : ℝ)| * (Ideal.absNorm I : ℝ) * U^2)) /
        (idealModuleTraceReconstructionConstant K I hI)^(Module.finrank ℚ K) := by
  have hD : 0 < |(NumberField.discr K : ℝ)| := abs_pos.mpr (by
    exact_mod_cast NumberField.discr_ne_zero K)
  have hN : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero ((Ideal.absNorm_eq_zero_iff).not.mpr hI)
  rw [idealModuleCoordinateSeparationRadius, div_pow,
    Real.rpow_inv_natCast_pow (le_of_lt (one_div_pos.mpr
      (mul_pos (mul_pos hD hN) (sq_pos_of_pos hU)))) (Module.finrank_pos.ne')]

theorem idealModuleCoordinateSeparationRadius_reciprocal_pow (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {U : ℝ} (hU : 0 < U) :
    (1/idealModuleCoordinateSeparationRadius K I hI U)^(Module.finrank ℚ K) =
      (idealModuleTraceReconstructionConstant K I hI)^(Module.finrank ℚ K) *
        |(NumberField.discr K : ℝ)| * (Ideal.absNorm I : ℝ) * U^2 := by
  rw [div_pow, one_pow, idealModuleCoordinateSeparationRadius_pow K I hI hU]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem idealModuleSieveReciprocalRadius_pow_le (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {U : ℝ} (hU : 0 < U) :
    (idealModuleSieveReciprocalRadius K I hI U)^(Module.finrank ℚ K) ≤
      1 + (idealModuleTraceReconstructionConstant K I hI)^(Module.finrank ℚ K) *
        |(NumberField.discr K : ℝ)| * (Ideal.absNorm I : ℝ) * U^2 := by
  have hC := idealModuleTraceReconstructionConstant_pos K I hI
  have hp := idealModuleCoordinateSeparationRadius_reciprocal_pow K I hI hU
  unfold idealModuleSieveReciprocalRadius
  rcases le_total 1 (1/idealModuleCoordinateSeparationRadius K I hI U) with h | h
  · rw [max_eq_right h, hp]
    linarith
  · rw [max_eq_left h, one_pow]
    have hn : 0 ≤ (idealModuleTraceReconstructionConstant K I hI)^(Module.finrank ℚ K) *
        |(NumberField.discr K : ℝ)| * (Ideal.absNorm I : ℝ) * U^2 := by
      positivity
    linarith

def idealModuleSieveScaleConstant (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (c : ℝ) : ℝ :=
  coordinateOptimizedSieveConstant (IdealModuleFrequencyIndex K I hI) *
    (c^(Module.finrank ℚ K) + 1 +
      (idealModuleTraceReconstructionConstant K I hI)^(Module.finrank ℚ K) *
        |(NumberField.discr K : ℝ)| * (Ideal.absNorm I : ℝ))

theorem idealModuleSieveScaleConstant_pos (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {c : ℝ} (hc : 0 ≤ c) : 0 < idealModuleSieveScaleConstant K I hI c := by
  have hC := idealModuleTraceReconstructionConstant_pos K I hI
  unfold idealModuleSieveScaleConstant
  exact mul_pos coordinateOptimizedSieveConstant_pos (by positivity)

theorem idealModuleSieveScale_bound (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {c X U : ℝ} (hc : 0 ≤ c) (hX : 1 ≤ X) (hU : 1 ≤ U) :
    coordinateOptimizedSieveConstant (IdealModuleFrequencyIndex K I hI) *
      ((c * X^((Module.finrank ℚ K : ℝ)⁻¹))^(Module.finrank ℚ K) +
        (idealModuleSieveReciprocalRadius K I hI U)^(Module.finrank ℚ K)) ≤
    idealModuleSieveScaleConstant K I hI c * (X + U^2) := by
  have hC := idealModuleTraceReconstructionConstant_pos K I hI
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hU2 : 1 ≤ U^2 := one_le_pow₀ hU
  have hc0 : 0 ≤ c^(Module.finrank ℚ K) := pow_nonneg hc _
  let b := (idealModuleTraceReconstructionConstant K I hI)^(Module.finrank ℚ K) *
    |(NumberField.discr K : ℝ)| * (Ideal.absNorm I : ℝ)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hQ : (idealModuleSieveReciprocalRadius K I hI U)^(Module.finrank ℚ K) ≤
      1 + b*U^2 := idealModuleSieveReciprocalRadius_pow_le K I hI hU0
  rw [mul_pow,Real.rpow_inv_natCast_pow hX0 (Module.finrank_pos.ne')]
  change _ ≤ (coordinateOptimizedSieveConstant (IdealModuleFrequencyIndex K I hI) *
    (c^(Module.finrank ℚ K)+1+b))*(X+U^2)
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ coordinateOptimizedSieveConstant_pos.le
  have hxpart : c^(Module.finrank ℚ K)*X ≤
      (c^(Module.finrank ℚ K)+1+b)*X :=
    mul_le_mul_of_nonneg_right (by linarith) hX0
  have hup : 1+b*U^2 ≤ (c^(Module.finrank ℚ K)+1+b)*U^2 := by
    nlinarith [mul_nonneg hc0 (sq_nonneg U)]
  nlinarith

end
end ArtinMatthews.VaryingKummerAnalytic
