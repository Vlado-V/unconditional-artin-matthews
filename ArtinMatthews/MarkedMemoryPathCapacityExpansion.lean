module

public import ArtinMatthews.MarkedMemoryPathLineExpansion
public import ArtinMatthews.MarkedMemoryActualCapacityTail
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact separation of the actual finite-cap choice sum from its
omitted signed scalar. Incompatible choices contribute zero by the
literal projective-line and endpoint-order factors. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n) (q : ℝ)

theorem markedMemoryPathPrimeChoiceWeight_nonzero_compatible
    (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
    (hw : markedMemoryPathPrimeChoiceWeight hZ d q c≠0) :
    MarkedMemoryPathChoicesCompatible d hZ c := by
  intro j p
  have hj := (Finset.prod_ne_zero_iff.mp hw) j (Finset.mem_univ j)
  have hp := (Finset.prod_ne_zero_iff.mp hj) p (Finset.mem_univ p)
  exact markedMemoryPrimeLifespanChoice_nonzero _ _ _ _ _ hp

theorem markedMemoryPathPrimeChoiceWeight_compatible_sum :
    (∑ c : MarkedMemoryPathPrimeChoices (P := P) (n := n),markedMemoryPathPrimeChoiceWeight hZ d q c)=
      ∑ c : {c : MarkedMemoryPathPrimeChoices (P := P) (n := n) //
        MarkedMemoryPathChoicesCompatible d hZ c},markedMemoryPathPrimeChoiceWeight hZ d q c.1 := by
  let f := markedMemoryPathPrimeChoiceWeight hZ d q
  let p := MarkedMemoryPathChoicesCompatible d hZ
  have hz : (∑ c : {c // ¬p c},f c.1)=0 := by
    apply Finset.sum_eq_zero
    intro c _
    by_contra hc
    exact c.2 (markedMemoryPathPrimeChoiceWeight_nonzero_compatible hZ d q c.1 hc)
  have hs := Fintype.sum_subtype_add_sum_subtype p f
  rw [hz,add_zero] at hs
  exact hs.symm

def markedMemoryPathCappedChoiceSum (B : ℕ) : ℝ :=
  ∑ c : {c : MarkedMemoryPathPrimeChoices (P := P) (n := n) //
    MarkedMemoryPathChoicesCompatible d hZ c},
      if MarkedMemoryPathCapacity hZ d c.1 c.2 B then markedMemoryPathPrimeChoiceWeight hZ d q c.1 else 0

theorem markedMemoryPathPrimeChoiceWeight_cap_split (B : ℕ) :
    (∑ c : MarkedMemoryPathPrimeChoices (P := P) (n := n),markedMemoryPathPrimeChoiceWeight hZ d q c)=
      markedMemoryPathCappedChoiceSum hZ d q B+markedMemoryPathCapacitySignedError hZ d q B := by
  rw [markedMemoryPathPrimeChoiceWeight_compatible_sum]
  unfold markedMemoryPathCappedChoiceSum markedMemoryPathCapacitySignedError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp only [add_zero,zero_add]

theorem markedMemoryPathIndependentExpectation_capped
    (hP : ∀ i j,i≠j → Disjoint (P i) (P j))
    (hb : ∀ j (p : P j),markedMemoryBaseline q n p.1≠0) (B : ℕ) :
    markedMemoryPathIndependentExpectation hZ d q=
      (∏ j,∏ p : P j,markedMemoryBaseline q n p.1)*
        (markedMemoryPathCappedChoiceSum hZ d q B+markedMemoryPathCapacitySignedError hZ d q B) := by
  rw [markedMemoryPathIndependentExpectation_choices hZ d hP q hb,
    markedMemoryPathPrimeChoiceWeight_cap_split hZ d q B]

end
end ArtinMatthews
