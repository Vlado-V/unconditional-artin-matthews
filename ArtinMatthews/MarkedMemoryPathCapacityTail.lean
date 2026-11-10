module

public import ArtinMatthews.MarkedMemoryPathOrphanTailData
public import ArtinMatthews.MarkedMemoryPathEndpointCapacity
public import ArtinMatthews.MarkedMemoryPathOverCapacity
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

/-! The actual finite-capacity error is dominated by the proved orphan
tail. The original signed scalar sum is retained before taking its
absolute value; compatibility and the literal pending cutoff are the
actual path predicates. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)

theorem markedMemoryPathCapacity_absolute_error (q : ℝ) (hq0 : 0≤q) (hq1 : q≤1)
    (ha : ∀ j (p : P j),0 ≤ markedMemoryLineBirthAtom q n p.1)
    (r : ℝ) (hr : 1≤r) (m : ℕ)
    (hbudget : Fintype.card J*((n+1)*(pads+1))+m≤B) :
    (∑ c : {c : MarkedMemoryPathPrimeChoices (P := P) (n := n) //
        MarkedMemoryPathChoicesCompatible d hZ c},
      if MarkedMemoryPathCapacity hZ d c.1 c.2 B then 0 else
        |markedMemoryPathPrimeChoiceWeight hZ d q c.1|) ≤
      markedMemoryPathActiveChoiceAbsoluteMass hZ d q *
        Real.exp (r*markedMemoryPathInactiveAtomMass d q*((n:ℝ)+1)^2)/r^(m+1) := by
  let F := fun c : MarkedMemoryPathPrimeChoices (P := P) (n := n) =>
    if m+1 ≤ markedMemoryPathOrphanCount d c then |markedMemoryPathPrimeChoiceWeight hZ d q c| else 0
  have hF (c : MarkedMemoryPathPrimeChoices (P := P) (n := n)) : 0≤F c := by
    dsimp only [F]
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  calc
    _ ≤ ∑ c : {c : MarkedMemoryPathPrimeChoices (P := P) (n := n) //
        MarkedMemoryPathChoicesCompatible d hZ c},F c.1 := by
      apply Finset.sum_le_sum
      intro c _
      change (if MarkedMemoryPathCapacity hZ d c.1 c.2 B then 0 else
        |markedMemoryPathPrimeChoiceWeight hZ d q c.1|)≤F c.1
      by_cases hc : MarkedMemoryPathCapacity hZ d c.1 c.2 B
      · calc
          _ = 0 := ite_eq_left hc
          _ ≤ _ := hF c.1
      · have hn := markedMemoryPath_overCapacity_orphan_threshold hZ d c.1 c.2 m hbudget hc
        calc
          _ = |markedMemoryPathPrimeChoiceWeight hZ d q c.1| := ite_eq_right hc
          _ = F c.1 := (ite_eq_left hn).symm
          _ ≤ _ := le_rfl
    _ ≤ ∑ c : MarkedMemoryPathPrimeChoices (P := P) (n := n),F c := by
      have hs := Fintype.sum_subtype_add_sum_subtype
        (fun c : MarkedMemoryPathPrimeChoices (P := P) (n := n) => MarkedMemoryPathChoicesCompatible d hZ c) F
      have hn : 0 ≤ ∑ c : {c : MarkedMemoryPathPrimeChoices (P := P) (n := n) //
          ¬MarkedMemoryPathChoicesCompatible d hZ c},F c.1 :=
        Finset.sum_nonneg (fun c _ => hF c.1)
      linarith
    _ ≤ _ := markedMemoryPathOrphan_absolute_tail hZ d q hq0 hq1 ha r hr (m+1)

theorem markedMemoryPathCapacity_signed_error (q : ℝ) (hq0 : 0≤q) (hq1 : q≤1)
    (ha : ∀ j (p : P j),0 ≤ markedMemoryLineBirthAtom q n p.1)
    (r : ℝ) (hr : 1≤r) (m : ℕ)
    (hbudget : Fintype.card J*((n+1)*(pads+1))+m≤B) :
    |∑ c : {c : MarkedMemoryPathPrimeChoices (P := P) (n := n) //
        MarkedMemoryPathChoicesCompatible d hZ c},
      if MarkedMemoryPathCapacity hZ d c.1 c.2 B then 0 else
        markedMemoryPathPrimeChoiceWeight hZ d q c.1| ≤
      markedMemoryPathActiveChoiceAbsoluteMass hZ d q *
        Real.exp (r*markedMemoryPathInactiveAtomMass d q*((n:ℝ)+1)^2)/r^(m+1) := by
  calc
    _ ≤ ∑ c : {c : MarkedMemoryPathPrimeChoices (P := P) (n := n) //
        MarkedMemoryPathChoicesCompatible d hZ c},
        |if MarkedMemoryPathCapacity hZ d c.1 c.2 B then 0 else
          markedMemoryPathPrimeChoiceWeight hZ d q c.1| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c : {c : MarkedMemoryPathPrimeChoices (P := P) (n := n) //
        MarkedMemoryPathChoicesCompatible d hZ c},
        if MarkedMemoryPathCapacity hZ d c.1 c.2 B then 0 else
          |markedMemoryPathPrimeChoiceWeight hZ d q c.1| := by
      apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> simp only [abs_zero]
    _ ≤ _ := markedMemoryPathCapacity_absolute_error hZ d q hq0 hq1 ha r hr m hbudget

end
end ArtinMatthews
