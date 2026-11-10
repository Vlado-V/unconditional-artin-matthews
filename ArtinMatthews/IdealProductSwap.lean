module

public import ArtinMatthews.IdealProductAverage
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

/-! Simultaneously swapping chosen coordinates preserves the two full
harmonic product laws exactly. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealLabelExpectation_swap {G A : Type*} [Fintype G] [DecidableEq G]
    [CommRing A] [Algebra ℝ A] (P : G → Finset ℕ) {M : ℕ}
    (S : Finset (G × Fin M))
    (F : MarkedPhysicalMarking P M → MarkedPhysicalMarking P M → A) :
    idealLabelExpectation P M (fun a => idealLabelExpectation P M
      (fun b => F (idealMix S a b) (idealMix S b a)))=
      idealLabelExpectation P M (fun a => idealLabelExpectation P M (F a)) := by
  have he := (idealMixEquiv (P:=P) S).sum_comp
    (fun z : MarkedPhysicalMarking P M × MarkedPhysicalMarking P M =>
      algebraMap ℝ A (idealLabelMass P M z.1*idealLabelMass P M z.2)*F z.1 z.2)
  simp only [idealMixEquiv,Equiv.coe_fn_mk,idealLabelMass_mix] at he
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type] at he
  unfold idealLabelExpectation
  simp only [mul_sum,← mul_assoc,← map_mul]
  exact he

theorem idealMix_eq_self_of_eq_outside {G : Type*} {P : G → Finset ℕ} {M : ℕ}
    (S : Finset (G × Fin M)) (a b : MarkedPhysicalMarking P M)
    (h : ∀ g i,(g,i)∉S → b g i=a g i) : idealMix S a b=b := by
  funext g i
  simp only [idealMix]
  split_ifs with hi
  · rfl
  · exact (h g i hi).symm

end
end ArtinMatthews
