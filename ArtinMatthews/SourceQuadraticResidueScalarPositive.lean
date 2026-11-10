module

public import ArtinMatthews.SourceQuadraticSmallResidue
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
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
public import OAI.NumberTheory.DirichletL.Detector.RadialMellin
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Reality and positivity of the residue scalar for the actual nonnegative
compact source weight. -/

namespace ArtinMatthews.SourceEulerAssembly

open NumberField MeasureTheory Set
open scoped NumberField Classical BigOperators

noncomputable section

theorem sourceQuadraticB2Bump_mellin_half_ofReal :
    mellin (fun t : ℝ => (sourceQuadraticB2Bump t : ℂ)) (1 / 2) =
      ((∫ t : ℝ in Ioi 0, t ^ ((1 / 2 : ℝ) - 1) * sourceQuadraticB2Bump t : ℝ) : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    OAI.SevenEighths.ProbeRadialMellin.mellin_real, ← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [Complex.real_smul, Complex.ofReal_mul]

theorem sourceQuadraticB2Bump_half_integral_nonneg :
    0 ≤ ∫ t : ℝ in Ioi 0, t ^ ((1 / 2 : ℝ) - 1) * sourceQuadraticB2Bump t := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (Real.rpow_nonneg ht.le _) (sourceQuadraticB2Bump_nonneg t)

variable (F : Type) [Field F] [NumberField F]

theorem sourceQuadraticSmallResidueFactor_ofReal (M : ℝ) :
    sourceQuadraticSmallResidueFactor F M =
      ((dedekindZeta_residue F * Real.sqrt M * ((1 / 2 : ℝ) *
        ∫ t : ℝ in Ioi 0, t ^ ((1 / 2 : ℝ) - 1) * sourceQuadraticB2Bump t) : ℝ) : ℂ) := by
  rw [sourceQuadraticSmallResidueFactor, sourceQuadraticB2Bump_mellin_half_ofReal]
  push_cast
  rfl

theorem sourceQuadraticSmallResidueFactor_nonnegative (M : ℝ) :
    0 ≤ (sourceQuadraticSmallResidueFactor F M).re ∧
      (sourceQuadraticSmallResidueFactor F M).im = 0 := by
  rw [sourceQuadraticSmallResidueFactor_ofReal]
  simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
  exact mul_nonneg
    (mul_nonneg (dedekindZeta_residue_pos F).le (Real.sqrt_nonneg M))
    (mul_nonneg (by norm_num) sourceQuadraticB2Bump_half_integral_nonneg)

end
end ArtinMatthews.SourceEulerAssembly
