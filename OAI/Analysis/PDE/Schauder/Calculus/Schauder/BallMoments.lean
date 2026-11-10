module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.RadialMoments


set_option backward.privateInPublic true
@[expose] public section

/-! Radial quadratic moments on a ball. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

def ballWeight (ρ : ℝ → ℝ) (R t : ℝ) : ℝ := (Iio R).indicator ρ t

variable {m : ℕ}

theorem ballWeight_integral (ρ : ℝ → ℝ) (R : ℝ) (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    (∫ y, ballWeight ρ R ‖y‖ * f y) = ∫ y in ball 0 R, ρ ‖y‖ * f y := by
  rw [← integral_indicator measurableSet_ball]
  congr 1
  funext y
  by_cases hy : ‖y‖ < R <;> simp [ballWeight, hy]

theorem ballMoment_offDiagonal (ρ : ℝ → ℝ) (R : ℝ) (i j : Fin m) (hij : i ≠ j) :
    (∫ y in ball 0 R, ρ ‖y‖ * (y : EuclideanSpace ℝ (Fin m)) i * y j) = 0 := by
  have h := radialMoment_offDiagonal (ballWeight ρ R) i j hij
  simpa only [radialMoment, mul_assoc, ballWeight_integral] using h

theorem ballMoment_diagonal_eq (ρ : ℝ → ℝ) (R : ℝ) (i j : Fin m) :
    (∫ y in ball 0 R, ρ ‖y‖ * (y : EuclideanSpace ℝ (Fin m)) i * y i) =
      ∫ y in ball 0 R, ρ ‖y‖ * (y : EuclideanSpace ℝ (Fin m)) j * y j := by
  have h := radialMoment_diagonal_eq (ballWeight ρ R) i j
  simpa only [radialMoment, mul_assoc, ballWeight_integral] using h

end OAI.Analysis.PDE.Schauder
