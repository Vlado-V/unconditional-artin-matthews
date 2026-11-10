module

public import ArtinMatthews.SpectralAmbientTestPairing
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

/-! Scalar normalization of the actual full ambient multiplier. -/

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

theorem gamma0AmbientTestOperator_smul (N : ℕ) [NeZero N]
    (c : ℂ) (h : SpectralEnergyTest) (v : Gamma0RegionL2 N) :
    gamma0AmbientTestOperator N (c • h) v = c • gamma0AmbientTestOperator N h v := by
  apply ext_inner_left ℂ
  intro u
  rw [inner_smul_right,gamma0AmbientTestOperator_pair,gamma0AmbientTestOperator_pair,
    mul_add,mul_add]
  congr 1
  · rw [← tsum_mul_left]
    apply tsum_congr
    intro i
    change (c*gamma0CuspidalTestSymbol N h i)*_ = c*(gamma0CuspidalTestSymbol N h i*_)
    ring
  · congr 1
    · rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      change (c*spectralContinuousTestSymbol h t)*_ = c*(spectralContinuousTestSymbol h t*_)
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      change (c*h l)*_ = c*(h l*_)
      ring

end ArtinMatthews
