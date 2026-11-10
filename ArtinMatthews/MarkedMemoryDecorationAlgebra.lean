module

public import ArtinMatthews.MarkedMemoryDecorationAverage
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

namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*} [∀ j,Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads n : ℕ} {Z : Finset (ℤ × ℤ)}
  (d : MarkedMemoryEndpointData A P pads Z n)

theorem markedMemoryDecoration_weighted_average (a c L : ℂ)
    (F : MarkedMemoryEndpointBirthOrders d → MarkedMemoryCopiedOrders (J := J) (pads := pads) (n := n) → ℂ) :
    (∑ b : MarkedMemoryEndpointBirthOrders d,∑ o : MarkedMemoryCopiedOrders (J := J) (pads := pads) (n := n),
      (a/(markedMemoryEndpointBirthFactorial d : ℂ))*c*F b o/L) =
    a*((markedMemoryCopiedOrderCount J pads n : ℂ)*c)*markedMemoryDecorationAverage d F/L := by
  have ht (b : MarkedMemoryEndpointBirthOrders d) (o : MarkedMemoryCopiedOrders (J := J) (pads := pads) (n := n)) :
      (a/(markedMemoryEndpointBirthFactorial d : ℂ))*c*F b o/L =
      (a*c/L)*(F b o/(markedMemoryEndpointBirthFactorial d : ℂ)) := by ring
  simp_rw [ht]
  simp only [← Finset.mul_sum,← Finset.sum_div]
  have h := congrArg (fun z : ℂ => (a*c/L)*z) (markedMemoryDecorationAverage_cancel_births d F)
  exact h.trans (by ring)

@[instance_reducible]
def markedMemoryDecorationBirthFintype : Fintype (MarkedMemoryEndpointBirthOrders d) := inferInstance

@[instance_reducible]
def markedMemoryDecorationCopyFintype :
    Fintype (MarkedMemoryCopiedOrders (J := J) (pads := pads) (n := n)) := inferInstance

/-- Instance-explicit transport prevents unfolding the large finite
carrier while comparing equivalent choices of its enumeration. -/
theorem markedMemoryDecoration_weighted_average_instances
    (iB : Fintype (MarkedMemoryEndpointBirthOrders d))
    (iO : Fintype (MarkedMemoryCopiedOrders (J := J) (pads := pads) (n := n)))
    (a c L : ℂ)
    (F : MarkedMemoryEndpointBirthOrders d → MarkedMemoryCopiedOrders (J := J) (pads := pads) (n := n) → ℂ) :
    (letI : Fintype (MarkedMemoryEndpointBirthOrders d) := iB
     letI : Fintype (MarkedMemoryCopiedOrders (J := J) (pads := pads) (n := n)) := iO
     ∑ b : MarkedMemoryEndpointBirthOrders d,∑ o : MarkedMemoryCopiedOrders (J := J) (pads := pads) (n := n),
       (a/(markedMemoryEndpointBirthFactorial d : ℂ))*c*F b o/L) =
    a*((markedMemoryCopiedOrderCount J pads n : ℂ)*c)*markedMemoryDecorationAverage d F/L := by
  have hb : iB=markedMemoryDecorationBirthFintype d := Subsingleton.elim _ _
  have ho : iO=markedMemoryDecorationCopyFintype (J := J) (pads := pads) (n := n) := Subsingleton.elim _ _
  subst iB
  subst iO
  exact markedMemoryDecoration_weighted_average d a c L F

end
end ArtinMatthews
