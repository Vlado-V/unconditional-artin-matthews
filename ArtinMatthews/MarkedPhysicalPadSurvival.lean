module

public import ArtinMatthews.MarkedPhysicalPadCollisionMass
public import ArtinMatthews.MarkedMajorLabelPolynomial
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The exact harmonic weight of each fixed pair of unshared labels.
The probability is formed after fixing both labels, so no adaptive
choice of labels enters the collision estimate. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalMass_two_labelMass_sq {J : Type*} [Fintype J] (P : J → Finset ℕ) :
    markedPhysicalMass (fun j => bandReciprocalMass (P j)) 2 = (markedMajorLabelMass P)^2 := by
  rw [markedPhysicalMass,markedMajorLabelMass,Finset.prod_pow]

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (pads : ℕ) (hV : ∀ j,0 < bandReciprocalMass (P j))
  (b a : (j : J) → ↥(P j))

include hV

theorem markedPhysicalPadHarmonicMass_survival :
    (∑ c : MarkedPhysicalMarking P pads,
      if ¬MarkedPhysicalPadCollisionEvent P pads b a c then
        markedPhysicalPadHarmonicMass P pads c else 0)=
      1-markedPhysicalPadCollisionMass P pads b a := by
  let μ := markedPhysicalPadHarmonicMass P pads
  let E := MarkedPhysicalPadCollisionEvent P pads b a
  have h (c : MarkedPhysicalMarking P pads) :
      (if ¬E c then μ c else 0) = μ c-(if E c then 1 else 0)*μ c := by
    by_cases hc : E c <;> simp [hc]
  change (∑ c,if ¬E c then μ c else 0)=_
  simp_rw [h]
  rw [Finset.sum_sub_distrib]
  change (∑ c,markedPhysicalPadHarmonicMass P pads c)-markedPhysicalPadCollisionMass P pads b a=_
  rw [markedPhysicalPadHarmonicMass_sum P pads hV]

theorem markedPhysicalPadHarmonicMass_survival_weighted (z : ℂ) :
    (∑ c : MarkedPhysicalMarking P pads,(markedPhysicalPadHarmonicMass P pads c:ℂ)*
      (if ¬MarkedPhysicalPadCollisionEvent P pads b a c then z else 0))=
      ((1-markedPhysicalPadCollisionMass P pads b a:ℝ):ℂ)*z := by
  rw [← markedPhysicalPadHarmonicMass_survival P pads hV b a,Complex.ofReal_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : MarkedPhysicalPadCollisionEvent P pads b a c <;> simp [hc]

end
end ArtinMatthews
