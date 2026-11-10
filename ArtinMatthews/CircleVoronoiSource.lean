module

public import ArtinMatthews.CircleShiftedFrequency
public import ArtinMatthews.ShiftedDoubleVoronoiKloosterman
public import ArtinMatthews.CircleSourceDetector
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Exact passage between a finitely supported source and the infinite-sum
notation of double Voronoi. All circle and congruence sums are finite. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem circle_source_sum (H d m3 m4 : ℕ) [NeZero H] [NeZero d]
    (v3 v4 : (ZMod (H*d))ˣ)
    (hv3 : (v3 : ZMod (H*d))=(m3 : ZMod (H*d)))
    (hv4 : (v4 : ZMod (H*d))=(m4 : ZMod (H*d)))
    (S : Finset (ℕ×ℕ)) (A : ℕ×ℕ → ℂ) (hzero : ∀ k∉S, A k=0) :
    (∑ a : (ZMod (H*d))ˣ, ∑ j : ZMod d, ∑' k : ℕ×ℕ,
      A k*ZMod.stdAddChar (doubleVoronoiSourceDetector H d v3 v4 a k.1 k.2 j))/(d : ℂ) =
      ∑ k∈S, A k*primitiveCircleSum (H*d) (circleShiftedFrequency m3 m4 k)*
        (if (d : ℤ)∣((k.1 : ℤ)-1) then 1 else 0) := by
  classical
  have hfinite (a : (ZMod (H*d))ˣ) (j : ZMod d) :
      (∑' k : ℕ×ℕ, A k*ZMod.stdAddChar (doubleVoronoiSourceDetector H d v3 v4 a k.1 k.2 j)) =
      ∑ k∈S, A k*ZMod.stdAddChar (doubleVoronoiSourceDetector H d v3 v4 a k.1 k.2 j) := by
    apply tsum_eq_sum
    intro k hk
    rw [hzero k hk,zero_mul]
  simp_rw [hfinite]
  have hswap : (∑ a : (ZMod (H*d))ˣ, ∑ j : ZMod d, ∑ k∈S,
      A k*ZMod.stdAddChar (doubleVoronoiSourceDetector H d v3 v4 a k.1 k.2 j)) =
      ∑ k∈S, A k*(∑ a : (ZMod (H*d))ˣ, ∑ j : ZMod d,
        ZMod.stdAddChar (doubleVoronoiSourceDetector H d v3 v4 a k.1 k.2 j)) := by
    simp_rw [Finset.mul_sum]
    calc
      _ = ∑ a : (ZMod (H*d))ˣ, ∑ k∈S, ∑ j : ZMod d,
          A k*ZMod.stdAddChar (doubleVoronoiSourceDetector H d v3 v4 a k.1 k.2 j) := by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hswap,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_div_assoc,circle_source_detector H d m3 m4 v3 v4 hv3 hv4 k]
  ring

end ArtinMatthews
