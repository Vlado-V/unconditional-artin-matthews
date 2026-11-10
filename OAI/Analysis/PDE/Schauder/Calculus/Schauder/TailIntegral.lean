module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Integrability and exact scaling of the far-field radial majorant. -/

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped Pointwise
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def rieszTailMass (μ : Measure E) (α : ℝ) : ℝ :=
  ∫ y in {y : E | 1 < ‖y‖}, ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ) - 1) ∂μ

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem rieszTailMass_nonneg (μ : Measure E) (α : ℝ) : 0 ≤ rieszTailMass μ α :=
  integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg y) _

theorem integrableOn_riesz_tail (μ : Measure E) [μ.IsAddHaarMeasure]
    (hd : 1 ≤ Module.finrank ℝ E) {α R : ℝ} (hα : α < 1) (hR : 0 < R) :
    IntegrableOn (fun y : E => ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ) - 1))
      {y : E | R < ‖y‖} μ := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  let g : ℝ → ℝ := (Ioi R).indicator (fun r => r ^ (α - (Module.finrank ℝ E : ℝ) - 1))
  have hscalar : IntegrableOn
      (fun r : ℝ => r ^ (Module.finrank ℝ E - 1) * r ^ (α - (Module.finrank ℝ E : ℝ) - 1))
      (Ioi R) := by
    apply (integrableOn_Ioi_rpow_of_lt (show α - 2 < -1 by linarith) hR).congr_fun _ measurableSet_Ioi
    intro r hr
    have hr0 : 0 < r := hR.trans hr
    dsimp only
    rw [← Real.rpow_natCast, ← Real.rpow_add hr0]
    congr 1
    rw [Nat.cast_sub hd]
    push_cast
    ring
  have hwhole := hscalar.integrable_indicator measurableSet_Ioi
  have heq (r : ℝ) : r ^ (Module.finrank ℝ E - 1) • g r =
      (Ioi R).indicator
        (fun r : ℝ => r ^ (Module.finrank ℝ E - 1) * r ^ (α - (Module.finrank ℝ E : ℝ) - 1)) r := by
    by_cases hr : R < r <;> simp [g, hr, smul_eq_mul]
  have hnorm : Integrable (fun y : E => g ‖y‖) μ := by
    apply (integrable_fun_norm_addHaar μ).mpr
    simpa only [heq, IntegrableOn] using! hwhole.restrict (s := Ioi (0 : ℝ))
  rw [← integrable_indicator_iff (measurableSet_lt measurable_const continuous_norm.measurable)]
  simpa [g, Set.indicator] using! hnorm

theorem integral_riesz_tail (μ : Measure E) [μ.IsAddHaarMeasure]
    (α : ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ y in {y : E | R < ‖y‖}, ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ) - 1) ∂μ) =
      R ^ (α - 1) * rieszTailMass μ α := by
  have he := μ.setIntegral_comp_smul_of_pos
    (fun y : E => ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ) - 1)) {y : E | 1 < ‖y‖} hR
  have himage : R • {y : E | 1 < ‖y‖} = {y : E | R < ‖y‖} := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hR.ne']
    simp only [Set.mem_ofPred_eq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    rw [← div_eq_inv_mul, lt_div_iff₀ hR, one_mul]
  have hf (y : E) : ‖R • y‖ ^ (α - (Module.finrank ℝ E : ℝ) - 1) =
      R ^ (α - (Module.finrank ℝ E : ℝ) - 1) * ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ) - 1) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR, Real.mul_rpow hR.le (norm_nonneg y)]
  simp only [himage, hf, integral_const_mul, smul_eq_mul] at he
  have hp : R ^ Module.finrank ℝ E * R ^ (α - (Module.finrank ℝ E : ℝ) - 1) = R ^ (α - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR]
    congr 1
    ring
  have hh := congrArg (fun t : ℝ => R ^ Module.finrank ℝ E * t) he
  rw [← mul_assoc, hp, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hR.ne'), one_mul] at hh
  exact hh.symm

end OAI.Analysis.PDE.Schauder
