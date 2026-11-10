module

public import ArtinMatthews.MarkedRootPartitionIntervals
public import OAI.NumberTheory.Jacobsthal.Estimates.SourcePairRemainder
public import ArtinMatthews.FixedURootWeightedGeometry
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Std.Tactic.BVDecide.Normalize.BitVec


set_option backward.privateInPublic true
@[expose] public section

/-! The half-open cell conventions match the actual arithmetic rectangle
flags exactly, including all integer endpoints. -/

noncomputable section
namespace ArtinMatthews
open OAI.Erdos970.ErdosHyperbolaError
attribute [local instance] Classical.propDecidable

theorem markedRoot_mem_integer_interval (A B : ℝ) (n : ℤ) (rc : Bool) :
    n ∈ realIntervalIntegers A B true rc ↔ A ≤ (n:ℝ) ∧
      if rc then (n:ℝ) ≤ B else (n:ℝ) < B := by
  cases rc
  · simp only [realIntervalIntegers,Finset.mem_filter,Finset.mem_Icc,Int.ceil_le,Int.le_floor,
      Bool.false_eq_true,ite_false,ite_true]
    constructor
    · rintro ⟨⟨hA,_⟩,_,hB⟩
      exact ⟨hA,hB⟩
    · rintro ⟨hA,hB⟩
      exact ⟨⟨hA,hB.le⟩,hA,hB⟩
  · simpa only [ite_true] using fixedURoot_mem_closed_interval A B n

theorem markedRootPartitionInterval_integer_iff (N K : ℕ) (i : Fin K)
    (s T : ℝ) (hT : 0 < T) (n : ℤ) :
    n ∈ realIntervalIntegers (T*(s+(i:ℝ)/N)) (T*(s+((i:ℝ)+1)/N)) true (decide ((i:ℕ)+1=K)) ↔
      (n:ℝ)/T ∈ markedRootPartitionInterval N K i s := by
  rw [markedRoot_mem_integer_interval]
  unfold markedRootPartitionInterval
  simp only [Set.mem_ofPred_eq]
  by_cases hi : (i:ℕ)+1=K
  · simp only [hi,decide_true,ite_true,le_div_iff₀ hT,div_le_iff₀ hT]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith
  · simp only [hi,decide_false,Bool.false_eq_true,ite_false,le_div_iff₀ hT,div_lt_iff₀ hT]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith

end ArtinMatthews
