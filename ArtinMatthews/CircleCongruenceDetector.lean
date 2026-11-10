module

public import ArtinMatthews.CircleDetector
public import ArtinMatthews.DoubleVoronoiDetection
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

/-! Compatibility of the integer-frequency circle approximation with the
exact normalized d-congruence detector used by double Voronoi summation. -/

noncomputable section
open scoped BigOperators
open OAI.Erdos970.ErdosKloosterman.PrimePower
namespace ArtinMatthews

theorem circle_residue_average (d : ℕ) [NeZero d] (x : ZMod d) :
    (∑ j : ZMod d, ZMod.stdAddChar (j*x))/(d : ℂ) =
      if x=0 then 1 else 0 := by
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar d)]
  simp only [ZMod.card]
  split_ifs <;> simp [show (d : ℂ)≠0 by exact_mod_cast NeZero.ne d]

theorem circle_lifted_congruence_average (H d : ℕ) [NeZero H] [NeZero d]
    (a : (ZMod (H*d))ˣ) (n x : ℤ) :
    (∑ j : ZMod d, ZMod.stdAddChar
      ((a : ZMod (H*d))*(n : ZMod (H*d)) +
        (H : ZMod (H*d))*(j.val : ZMod (H*d))*(x : ZMod (H*d))))/(d : ℂ) =
      ZMod.stdAddChar ((a : ZMod (H*d))*(n : ZMod (H*d))) *
        (if (d : ℤ)∣x then 1 else 0) := by
  classical
  simp_rw [doubleVoronoi_lifted_character]
  have hred : reduction H d (x : ZMod (H*d)) = (x : ZMod d) := map_intCast _ _
  simp_rw [hred]
  rw [← Finset.mul_sum,mul_div_assoc,circle_residue_average]
  simp only [ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem circle_with_congruence_exact (H d : ℕ) [NeZero H] [NeZero d]
    (n x : ℤ) :
    (∑ a : (ZMod (H*d))ˣ, ∑ j : ZMod d, ZMod.stdAddChar
      ((a : ZMod (H*d))*(n : ZMod (H*d)) +
        (H : ZMod (H*d))*(j.val : ZMod (H*d))*(x : ZMod (H*d))))/(d : ℂ) =
      primitiveCircleSum (H*d) n * (if (d : ℤ)∣x then 1 else 0) := by
  classical
  rw [Finset.sum_div]
  simp_rw [circle_lifted_congruence_average]
  rw [← Finset.sum_mul,primitiveCircleSum_eq]
  congr 1
  unfold OAI.JointDickman.ramanujanSum
  apply Finset.sum_congr rfl
  intro a _ha
  congr 1
  ring

end ArtinMatthews
