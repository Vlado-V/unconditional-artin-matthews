module

public import ArtinMatthews.MarkedFiniteEvenMomentPaths
public import ArtinMatthews.MarkedPhysicalLocalizedMoment
public import ArtinMatthews.MarkedPhysicalMomentTrace
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

/-! The genuine constant-mass physical even moment, expanded over all
physical states at all visits, with only endpoint positions identified. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

abbrev MarkedPhysicalMomentPath {J : Type*} (P : J → Finset ℕ)
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (R : ℕ) :=
  Fin (2*R+1) → MarkedPhysicalState P M Z

theorem markedPhysicalPositionMoment_paths
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (V : J → ℝ) (hV : ∀ j,0≤V j)
    (A : Matrix (MarkedPhysicalState P M Z) (MarkedPhysicalState P M Z) ℂ) (R : ℕ) :
    markedPhysicalPositionMoment P M Z V A R =
      markedPhysicalMass V M *
        (∑ p : MarkedPhysicalMomentPath P M Z R,
          if (p 0).1.1=(p (Fin.last (2*R))).1.1 then
            markedMatrixPathWeight (markedAlternatingMatrix A) (2*R) 0 p else 0).re := by
  rw [markedPhysicalPositionMoment_eq_original_mass P M Z V hV A R]
  congr 1
  exact markedEvenMoment_position_trace_paths A
    (fun s : MarkedPhysicalState P M Z => s.1.1) R

theorem markedPhysicalMomentPath_primitive {J : Type*}
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (R : ℕ)
    (p : MarkedPhysicalMomentPath P M Z R) (v : Fin (2*R+1)) :
    IsCoprime (p v).1.1.1.1 (p v).1.1.1.2 := (p v).2.1

theorem markedPhysicalMomentPath_distinct_lists {J : Type*}
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (R : ℕ)
    (p : MarkedPhysicalMomentPath P M Z R) (v : Fin (2*R+1)) :
    MarkedPhysicalMarkingDistinct (p v).1.2 := (p v).2.2.1

theorem markedPhysicalMomentPath_active_divides {J : Type*}
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (R : ℕ)
    (p : MarkedPhysicalMomentPath P M Z R) (v : Fin (2*R+1)) (j : J) (k : Fin M) :
    (((p v).1.2 j k : ℕ):ℤ)∣(p v).1.1.1.1 := (p v).2.2.2 j k

end
end ArtinMatthews
