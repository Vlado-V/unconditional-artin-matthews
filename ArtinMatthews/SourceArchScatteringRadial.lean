module

public import ArtinMatthews.SourceComplexTraceFourier
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact radial integration for the complex trace measure. -/
namespace ArtinMatthews.SourceArchJacquet

open MeasureTheory MeasureTheory.Measure Set
open ArtinMatthews.VaryingKummerAnalytic
noncomputable section

theorem sourceArchTraceIntegral_radial (f : ℝ → ℂ) :
    (∫ z : ℂ, f ‖z‖ ∂sourceComplexTraceMeasure) =
      (4 * Real.pi : ℝ) * ∫ r : ℝ in Ioi 0, (r : ℂ) * f r := by
  have hp : (∫ z : ℂ, f ‖z‖) =
      (2 * Real.pi : ℝ) * ∫ r : ℝ in Ioi 0, (r : ℂ) * f r := by
    calc
      _ = ∫ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, (p.1 : ℂ) * f |p.1| := by
        simpa only [polarCoord_target, Complex.norm_polarCoord_symm, Complex.real_smul] using
          (Complex.integral_comp_polarCoord_symm (fun z : ℂ => f ‖z‖)).symm
      _ = (∫ r : ℝ in Ioi 0, (r : ℂ) * f |r|) * ∫ _ : ℝ in Ioo (-Real.pi) Real.pi, (1 : ℂ) := by
        rw [← setIntegral_prod_mul, volume_eq_prod]
        simp only [mul_one]
      _ = _ := by
        have he : (∫ r : ℝ in Ioi 0, (r : ℂ) * f |r|) = ∫ r : ℝ in Ioi 0, (r : ℂ) * f r := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro r hr
          dsimp only
          rw [abs_of_pos hr]
        rw [he, integral_const, measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter,
          Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
        simp only [Complex.real_smul, mul_one]
        push_cast
        ring
  unfold sourceComplexTraceMeasure
  rw [integral_smul_measure, hp]
  norm_num
  ring

theorem sourceArchRadialIntegral_square (f : ℝ → ℂ) :
    (∫ r : ℝ in Ioi 0, (r : ℂ) * f (r ^ 2)) =
      (1 / 2 : ℂ) * ∫ t : ℝ in Ioi 0, f t := by
  have h := integral_comp_rpow_Ioi_of_pos (g := f) (by norm_num : (0 : ℝ) < 2)
  have he : (fun r : ℝ => ((2 : ℝ) * r ^ ((2 : ℝ) - 1)) • f (r ^ (2 : ℝ))) =
      (fun r : ℝ => (2 : ℂ) * ((r : ℂ) * f (r ^ 2))) := by
    funext r
    norm_num [smul_eq_mul]
    ring
  rw [he, integral_const_mul] at h
  calc
    _ = (1 / 2 : ℂ) * ((2 : ℂ) * ∫ r : ℝ in Ioi 0, (r : ℂ) * f (r ^ 2)) := by ring
    _ = _ := by rw [h]

theorem sourceArchIntegral_shift_one (f : ℝ → ℂ) :
    (∫ t : ℝ in Ioi 0, f (1 + t)) = ∫ t : ℝ in Ioi 1, f t := by
  have h := integral_add_left_eq_self (μ := (volume : Measure ℝ)) (fun t : ℝ => (Ioi 1).indicator f t) (1 : ℝ)
  have he : (fun t : ℝ => (Ioi 1).indicator f (1 + t)) =
      (Ioi 0).indicator (fun t => f (1 + t)) := by
    funext t
    by_cases ht : 0 < t
    · have ht' : 1 < 1 + t := by linarith
      simp [ht, ht']
    · have ht' : ¬ 1 < 1 + t := by linarith
      simp [ht, ht']
  rw [he, integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Ioi] at h
  exact h

end
end ArtinMatthews.SourceArchJacquet
