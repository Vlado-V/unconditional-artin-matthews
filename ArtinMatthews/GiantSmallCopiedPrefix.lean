module

public import ArtinMatthews.GiantSmallConditioningData
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


set_option backward.privateInPublic true
@[expose] public section

/-! Two full small marking lists with a common copied prefix have an
exact ordered-prefix and independent-tail parametrization. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} {P : J → Finset ℕ} {k ell : ℕ}

def giantSmallPrefix (a : MarkedPhysicalMarking P (k+ell)) :
    MarkedPhysicalMarking P k := fun j i => a j (Fin.castAdd ell i)

theorem giantSmallPrefix_append (d : MarkedPhysicalMarking P k)
    (r : MarkedPhysicalMarking P ell) :
    giantSmallPrefix (giantSmallAppend d r) = d := by
  funext j i
  exact Fin.append_left _ _ i

variable [Fintype J] [DecidableEq J]

theorem giantSmallCopiedTarget_sum (a : MarkedPhysicalMarking P (k+ell))
    (F : MarkedPhysicalMarking P (k+ell) → ℂ) :
    (∑ b : MarkedPhysicalMarking P (k+ell),
      if giantSmallPrefix b = giantSmallPrefix a then F b else 0) =
        ∑ r : MarkedPhysicalMarking P ell, F (giantSmallAppend (giantSmallPrefix a) r) := by
  rw [← giantSmallAppend_sum (f := fun b =>
    if giantSmallPrefix b = giantSmallPrefix a then F b else 0)]
  simp only [giantSmallPrefix_append]
  rw [Finset.sum_eq_single (giantSmallPrefix a)]
  · simp
  · intro d _ hd
    simp only [hd, ite_false, Finset.sum_const_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem giantSmallCopiedPair_sum
    (F : MarkedPhysicalMarking P (k+ell) → MarkedPhysicalMarking P (k+ell) → ℂ) :
    (∑ a : MarkedPhysicalMarking P (k+ell), ∑ b : MarkedPhysicalMarking P (k+ell),
      if giantSmallPrefix b = giantSmallPrefix a then F a b else 0) =
      ∑ d : MarkedPhysicalMarking P k, ∑ r : MarkedPhysicalMarking P ell,
        ∑ r' : MarkedPhysicalMarking P ell, F (giantSmallAppend d r) (giantSmallAppend d r') := by
  simp_rw [giantSmallCopiedTarget_sum]
  rw [← giantSmallAppend_sum (f := fun a =>
    ∑ r' : MarkedPhysicalMarking P ell, F a (giantSmallAppend (giantSmallPrefix a) r'))]
  simp only [giantSmallPrefix_append]

end
end ArtinMatthews
