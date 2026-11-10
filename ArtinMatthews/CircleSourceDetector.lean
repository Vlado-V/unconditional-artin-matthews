module

public import ArtinMatthews.CircleShiftedFrequency
public import ArtinMatthews.ShiftedDoubleVoronoiKloosterman
public import ArtinMatthews.CircleCongruenceDetector
public import ArtinMatthews.CircleFiniteApproximation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The original shifted source detector equals the Ramanujan detector times
the exact integrality condition. No new congruence convention is introduced. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem circle_source_detector (H d m3 m4 : ℕ) [NeZero H] [NeZero d]
    (v3 v4 : (ZMod (H*d))ˣ)
    (hv3 : (v3 : ZMod (H*d))=(m3 : ZMod (H*d)))
    (hv4 : (v4 : ZMod (H*d))=(m4 : ZMod (H*d))) (k : ℕ×ℕ) :
    (∑ a : (ZMod (H*d))ˣ, ∑ j : ZMod d,
      ZMod.stdAddChar (doubleVoronoiSourceDetector H d v3 v4 a k.1 k.2 j))/(d : ℂ) =
    primitiveCircleSum (H*d) (circleShiftedFrequency m3 m4 k) *
      (if (d : ℤ)∣((k.1 : ℤ)-1) then 1 else 0) := by
  convert circle_with_congruence_exact H d
    (circleShiftedFrequency m3 m4 k) ((k.1 : ℤ)-1) using 1
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [doubleVoronoiSourceDetector,circleShiftedFrequency,hv3,hv4,
    Int.cast_sub,Int.cast_mul,Int.cast_natCast,Int.cast_one]

theorem circleDetector_finite_congruence_approximation {ι : Type*}
    (S : Finset ι) (a : ι → ℂ) (frequency congruence : ι → ℤ) (d : ℕ)
    (Q : Finset ℕ) (ω : ℕ → ℝ)
    (hω : ∀ q∈Q, 0≤ω q) (hΛ : 0<circleNormalizer Q ω)
    (R : ℕ) (hR : ∀ i∈S, (frequency i).natAbs≤R) :
    ‖(∑ i∈S with (d : ℤ)∣congruence i, a i*circleDetector Q ω (frequency i)) -
      (∑ i∈S with frequency i=0 ∧ (d : ℤ)∣congruence i, a i)‖ ≤
      (∑ i∈S, ‖a i‖) * (circleWeightMass Q ω*(R : ℝ)^2/circleNormalizer Q ω) := by
  classical
  have hf := circleDetector_finite_approximation (S.filter (fun i => (d : ℤ)∣congruence i))
    a frequency Q ω hω hΛ R (fun i hi => hR i (Finset.mem_filter.mp hi).1)
  have hsets : (S.filter (fun i => (d : ℤ)∣congruence i)).filter (fun i => frequency i=0) =
      S.filter (fun i => frequency i=0 ∧ (d : ℤ)∣congruence i) := by
    ext i
    simp only [Finset.mem_filter]
    tauto
  rw [hsets] at hf
  apply hf.trans
  apply mul_le_mul_of_nonneg_right
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => norm_nonneg _)
  · exact div_nonneg (mul_nonneg (circleWeightMass_nonneg Q ω hω) (sq_nonneg _)) hΛ.le

end ArtinMatthews
