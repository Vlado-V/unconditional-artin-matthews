module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! One actual fixed nonnegative compact smooth majorant for the dyadic
prime interval, independent of every field, prime q and scale x. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory Set
open scoped ContDiff
noncomputable section

def splitPrimeBump : ContDiffBump (3/2 : ℝ) where
  rIn := 1/2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def splitPrimeWeight (y : ℝ) : ℂ := (splitPrimeBump y : ℂ)

theorem splitPrimeWeight_compact : HasCompactSupport splitPrimeWeight :=
  splitPrimeBump.hasCompactSupport.comp_left Complex.ofReal_zero

theorem splitPrimeWeight_smooth : ContDiff ℝ ∞ splitPrimeWeight :=
  Complex.ofRealCLM.contDiff.comp splitPrimeBump.contDiff

theorem splitPrimeWeight_nonneg (y : ℝ) : 0 ≤ (splitPrimeWeight y).re :=
  splitPrimeBump.nonneg

theorem splitPrimeWeight_positive_support : tsupport splitPrimeWeight ⊆ Ioi 0 := by
  have ht : tsupport splitPrimeWeight ⊆ tsupport splitPrimeBump :=
    tsupport_comp_subset Complex.ofReal_zero _
  rw [splitPrimeBump.tsupport_eq] at ht
  intro y hy
  have h := ht hy
  rw [Metric.mem_closedBall,Real.dist_eq] at h
  change |y-3/2| ≤ 1 at h
  have H := (abs_le.mp h).1
  change 0 < y
  linarith

theorem splitPrimeWeight_eq_one (y : ℝ) (hy : y ∈ Icc (1 : ℝ) 2) :
    splitPrimeWeight y = 1 := by
  have h : y ∈ Metric.closedBall (3/2 : ℝ) splitPrimeBump.rIn := by
    rw [Metric.mem_closedBall,Real.dist_eq]
    change |y-3/2| ≤ 1/2
    exact abs_le.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩
  simp only [splitPrimeWeight,splitPrimeBump.one_of_mem_closedBall h,Complex.ofReal_one]

theorem splitPrimeWeight_majorant (y : ℝ) (hy : y ∈ Icc (1 : ℝ) 2) :
    1 ≤ (splitPrimeWeight y).re := by rw [splitPrimeWeight_eq_one y hy]; norm_num

end
end ArtinMatthews.VaryingKummerAnalytic
