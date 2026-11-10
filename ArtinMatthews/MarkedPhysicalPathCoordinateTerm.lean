module

public import ArtinMatthews.MarkedPhysicalPositionRootReindex
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

/-! Literal lifted path weights at a fixed ordered marking array and
canonical root. Invalid physical lifts have exactly zero weight. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

def markedPhysicalPathCoordinateTerm {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M n : ℕ} {Z : Finset (ℤ × ℤ)}
    (F : (Fin (n+1) → MarkedPhysicalState P M Z) → ℂ)
    (a : MarkedPhysicalLabelPath P M n)
    {S : ℕ} {A B C D : ℝ} (r : MarkedPhysicalCanonicalRoot S A B C D)
    (tail : Fin n → ℤ × ℤ) : ℂ :=
  markedPhysicalPositionPathExtend (fun pos => markedPhysicalPathArrayExtend F pos a)
    (Fin.cons (α := fun _ : Fin (n+1) => ℤ × ℤ) (markedPhysicalCanonicalRootPosition r)
      (fun v => markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r)
        (markedPhysicalCanonicalCompletion r) (tail v)))

theorem markedPhysicalPathCoordinateTerm_ne_zero_lift_mem
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {M n : ℕ} {Z : Finset (ℤ × ℤ)}
    (F : (Fin (n+1) → MarkedPhysicalState P M Z) → ℂ)
    (a : MarkedPhysicalLabelPath P M n)
    {S : ℕ} {A B C D : ℝ} (r : MarkedPhysicalCanonicalRoot S A B C D)
    (tail : Fin n → ℤ × ℤ) (h : markedPhysicalPathCoordinateTerm F a r tail≠0) (v : Fin n) :
    markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r)
      (markedPhysicalCanonicalCompletion r) (tail v)∈Z := by
  unfold markedPhysicalPathCoordinateTerm markedPhysicalPositionPathExtend at h
  split_ifs at h with hp
  · exact hp v.succ
  · exact False.elim (h rfl)

theorem markedPhysicalPathCoordinateTerm_ne_zero_image_mem
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {M n : ℕ} {Z : Finset (ℤ × ℤ)}
    (F : (Fin (n+1) → MarkedPhysicalState P M Z) → ℂ)
    (a : MarkedPhysicalLabelPath P M n)
    {S : ℕ} [NeZero S] {A B C D : ℝ} (hA : 1<A) (hC : 1<C)
    (r : MarkedPhysicalCanonicalRoot S A B C D) (tail : Fin n → ℤ × ℤ)
    (h : markedPhysicalPathCoordinateTerm F a r tail≠0) (v : Fin n) :
    tail v∈markedPhysicalCanonicalTargets hA hC r Z := by
  apply (markedPhysicalCanonicalTargets_mem hA hC r Z (tail v)).mpr
  exact markedPhysicalPathCoordinateTerm_ne_zero_lift_mem F a r tail h v

end
end ArtinMatthews
