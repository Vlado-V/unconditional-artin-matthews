module

public import ArtinMatthews.MarkedPhysicalRootChangeModulus
public import ArtinMatthews.MarkedPhysicalCoordinateIndexDamping
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

/-! The literal zero-extended physical path and damping sums can be
reindexed by any positive residue modulus without changing coordinates,
ordered labels, endpoint tests, or the original q factors. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalPathCoordinateTerm_changeModulus
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {M n : ℕ}
    {Z : Finset (ℤ × ℤ)} (F : (Fin (n+1) → MarkedPhysicalState P M Z) → ℂ)
    (a : MarkedPhysicalLabelPath P M n)
    (S T : ℕ) [NeZero S] [NeZero T] {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (r : MarkedPhysicalCanonicalRoot S A B C D) (tail : Fin n → ℤ × ℤ) :
    markedPhysicalPathCoordinateTerm F a (markedPhysicalCanonicalRootChangeModulus S T hA hC r) tail=
      markedPhysicalPathCoordinateTerm F a r tail := by
  unfold markedPhysicalPathCoordinateTerm
  rw [markedPhysicalCanonicalRootChangeModulus_position,markedPhysicalCanonicalRootChangeModulus_completion]

theorem markedPhysicalPathCoordinateTerm_sum_changeModulus
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {M n : ℕ}
    {Z : Finset (ℤ × ℤ)} (F : (Fin (n+1) → MarkedPhysicalState P M Z) → ℂ)
    (a : MarkedPhysicalLabelPath P M n)
    (S T : ℕ) [NeZero S] [NeZero T] {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (tail : Fin n → ℤ × ℤ) :
    (∑ r : MarkedPhysicalCanonicalRoot S A B C D,markedPhysicalPathCoordinateTerm F a r tail)=
      ∑ r : MarkedPhysicalCanonicalRoot T A B C D,markedPhysicalPathCoordinateTerm F a r tail := by
  calc
    _ = ∑ r : MarkedPhysicalCanonicalRoot S A B C D,
        markedPhysicalPathCoordinateTerm F a (markedPhysicalCanonicalRootChangeModulus S T hA hC r) tail := by
      simp only [markedPhysicalPathCoordinateTerm_changeModulus]
    _ = _ := Equiv.sum_comp (markedPhysicalCanonicalRootChangeModulus S T hA hC)
      (fun r : MarkedPhysicalCanonicalRoot T A B C D => markedPhysicalPathCoordinateTerm F a r tail)

theorem markedPhysicalCoordinateIndexDamping_changeModulus
    {J : Type*} [Fintype J] [DecidableEq J] (P : J → Finset ℕ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (q : ℝ)
    (G : MarkedPhysicalState P (pads+1) Z → Prop) {n B₀ : ℕ}
    (i : MarkedPhysicalCoordinateIndex P (pads+1) n B₀)
    (S T : ℕ) [NeZero S] [NeZero T] {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (r : MarkedPhysicalCanonicalRoot S A B C D) :
    markedPhysicalCoordinateIndexDamping P pads Z q G i
        (markedPhysicalCanonicalRootChangeModulus S T hA hC r)=
      markedPhysicalCoordinateIndexDamping P pads Z q G i r :=
  markedPhysicalPathCoordinateTerm_changeModulus _ _ S T hA hC r _

theorem markedPhysicalCoordinateIndexDamping_sum_changeModulus
    {J : Type*} [Fintype J] [DecidableEq J] (P : J → Finset ℕ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (q : ℝ)
    (G : MarkedPhysicalState P (pads+1) Z → Prop) {n B₀ : ℕ}
    (i : MarkedPhysicalCoordinateIndex P (pads+1) n B₀)
    (S T : ℕ) [NeZero S] [NeZero T] {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C) :
    (∑ r : MarkedPhysicalCanonicalRoot S A B C D,markedPhysicalCoordinateIndexDamping P pads Z q G i r)=
      ∑ r : MarkedPhysicalCanonicalRoot T A B C D,markedPhysicalCoordinateIndexDamping P pads Z q G i r :=
  markedPhysicalPathCoordinateTerm_sum_changeModulus _ _ S T hA hC _

end
end ArtinMatthews
