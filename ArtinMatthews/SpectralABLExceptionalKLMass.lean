module

public import ArtinMatthews.SpectralABLBareDiagonal
public import ArtinMatthews.SpectralABLExceptionalBound
public import ArtinMatthews.SpectralABLBareIntegrability
public import ArtinMatthews.SpectralABLExceptionalMassBound
public import ArtinMatthews.SpectralABLWindowFirstMoments
public import ArtinMatthews.SpectralABLWindowPositivity
public import ArtinMatthews.SpectralABLWindowSmooth
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

theorem spectralABLExceptionalCorrected_mass_le (a : ℝ) {A : ℕ} (hA : 3 ≤ A) :
    (∫ t : ℝ, ‖spectralABLExceptionalCorrected a A (t : ℂ)‖ ∂spectralKLSpectralMeasure) ≤
      spectralABLExceptionalBound A / Real.pi := by
  have hm : Measurable (fun t : ℝ => spectralABLExceptionalCorrected a A (t : ℂ)) :=
    (spectralABLExceptionalCorrected_real_contDiff a (show 1 ≤ A by omega)).continuous.measurable
  have htransfer := spectralKLCosh_integral_norm_le
    (fun t : ℝ => spectralABLExceptionalCorrected a A (t : ℂ))
    (spectralABLExceptionalWindowReal a A) hm
    (fun t _ => spectralABLExceptionalWindowReal_nonneg a A t)
    (spectralABLExceptionalWindowReal_first_moment_integrable a hA)
    (fun t _ => (spectralABLExceptionalCorrected_norm_real a A t).le)
  refine htransfer.trans ?_
  calc
    _ ≤ (2 / Real.pi ^ 2) * (spectralABLExceptionalBound A * (Real.pi / 2)) :=
      mul_le_mul_of_nonneg_left (spectralABLExceptionalWindowReal_first_moment_integral_le a hA)
        (by positivity)
    _ = _ := by field_simp [Real.pi_ne_zero] <;> ring

theorem spectralABLExceptionalBareDiagonal_norm_le (a : ℝ) {A : ℕ} (hA : 3 ≤ A) :
    ‖spectralABLBareDiagonal (spectralABLExceptionalCorrected a A)‖ ≤
      spectralABLExceptionalBound A / Real.pi := by
  exact (norm_integral_le_integral_norm _).trans (spectralABLExceptionalCorrected_mass_le a hA)

theorem spectralABLExceptionalHeatDiagonal_uniform_norm_le
    (a : ℝ) {A : ℕ} (hA : 3 ≤ A) (R : ℝ) :
    ‖spectralABLHeatDiagonal (spectralABLExceptionalCorrected a A) R‖ ≤
      spectralABLExceptionalBound A / Real.pi := by
  exact (spectralABLHeatDiagonal_norm_le _
    (spectralABLExceptionalCorrected_integrable a A hA) R).trans
      (spectralABLExceptionalCorrected_mass_le a hA)

end
end ArtinMatthews
