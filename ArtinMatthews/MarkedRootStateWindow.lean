module

public import ArtinMatthews.MarkedRawGoodRootTransport
public import ArtinMatthews.MarkedRootPartitionBox
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal finite state window selected by one normalized physical
root box. Its first-coordinate test supplies exactly the uniform tau
geometry needed by the signed memory-word estimate. -/

noncomputable section
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

def markedRootStateWindow (Z : Finset (ℤ × ℤ)) (U V : ℝ)
    (p : ℝ × (ℝ × ℝ)) : Finset (ℤ × ℤ) :=
  Z.filter (fun z => MarkedRootPhysicalBox U V (markedRootIntegerVector z) p)

theorem markedRootStateWindow_subset (Z : Finset (ℤ × ℤ)) (U V : ℝ)
    (p : ℝ × (ℝ × ℝ)) : markedRootStateWindow Z U V p ⊆ Z :=
  Finset.filter_subset _ _

theorem markedRootStateWindow_mem (Z : Finset (ℤ × ℤ)) (U V : ℝ)
    (p : ℝ × (ℝ × ℝ)) (z : ℤ × ℤ) :
    z ∈ markedRootStateWindow Z U V p ↔
      z ∈ Z ∧ MarkedRootPhysicalBox U V (markedRootIntegerVector z) p :=
  Finset.mem_filter

theorem markedRootStateWindow_origin (Z : Finset (ℤ × ℤ)) (U V : ℝ)
    (p : ℝ × (ℝ × ℝ)) (hp : p ∈ markedRootBoxDomain) (hz : (1,0) ∈ Z) :
    (1,0) ∈ markedRootStateWindow Z U V p := by
  apply Finset.mem_filter.mpr
  refine ⟨hz,?_⟩
  simpa only [MarkedRootPhysicalBox,markedRootBoxFirst,markedRootBoxSecond,
    markedTau,markedRootIntegerVector,Matrix.cons_val_zero,Matrix.cons_val_one,
    Int.cast_one,Int.cast_zero,mul_zero,add_zero,mul_one,zero_div] using
    (show p.2.1 ∈ Set.Icc (1:ℝ) 16 ∧ p.2.2 ∈ Set.Icc (1:ℝ) 2 from hp.2)

theorem markedRootStateWindow_tau_scaled (Z : Finset (ℤ × ℤ)) (U V : ℝ)
    (p : ℝ × (ℝ × ℝ)) (z : markedRootStateWindow Z U V p) :
    1 ≤ p.2.1*markedMinorIntegerTau p.1 z.1 ∧
      p.2.1*markedMinorIntegerTau p.1 z.1 ≤ 16 := by
  have h := (Finset.mem_filter.mp z.2).2.1
  simpa only [markedRootBoxFirst,markedTau,markedRootIntegerVector,
    markedMinorIntegerTau,Matrix.cons_val_zero,Matrix.cons_val_one,Set.mem_Icc] using h

theorem markedRootStateWindow_tau_bounds (Z : Finset (ℤ × ℤ)) (U V : ℝ)
    (p : ℝ × (ℝ × ℝ)) (hp : p ∈ markedRootBoxDomain)
    (z : markedRootStateWindow Z U V p) :
    (1/16:ℝ) ≤ markedMinorIntegerTau p.1 z.1 ∧
      markedMinorIntegerTau p.1 z.1 ≤ 16 := by
  have ha : 0 < p.2.1 := lt_of_lt_of_le (by norm_num) hp.2.1.1
  have h := markedRootStateWindow_tau_scaled Z U V p z
  have ht : 0 < markedMinorIntegerTau p.1 z.1 := by
    apply (mul_pos_iff_of_pos_left ha).mp
    exact lt_of_lt_of_le (by norm_num) h.1
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hp.2.1.2 ht.le]
  · nlinarith [mul_le_mul_of_nonneg_right hp.2.1.1 ht.le]

theorem markedRootStateWindow_tau_ratio (Z : Finset (ℤ × ℤ)) (U V : ℝ)
    (p : ℝ × (ℝ × ℝ)) (hp : p ∈ markedRootBoxDomain)
    (z v : markedRootStateWindow Z U V p) :
    |markedMinorIntegerTau p.1 v.1/markedMinorIntegerTau p.1 z.1| ≤ 16 := by
  have hz := markedRootStateWindow_tau_scaled Z U V p z
  have hv := markedRootStateWindow_tau_scaled Z U V p v
  have ha : 0 < p.2.1 := lt_of_lt_of_le (by norm_num) hp.2.1.1
  have hzt : 0 < markedMinorIntegerTau p.1 z.1 :=
    lt_of_lt_of_le (by norm_num) (markedRootStateWindow_tau_bounds Z U V p hp z).1
  have hvt : 0 ≤ markedMinorIntegerTau p.1 v.1 :=
    le_trans (by norm_num) (markedRootStateWindow_tau_bounds Z U V p hp v).1
  rw [abs_of_nonneg (div_nonneg hvt hzt.le),div_le_iff₀ hzt]
  apply (mul_le_mul_iff_of_pos_left ha).mp
  nlinarith

end ArtinMatthews
