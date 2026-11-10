module

public import ArtinMatthews.MarkedMemoryPrimeOrphanTail
public import ArtinMatthews.MarkedMemoryPathPrimeCount
public import ArtinMatthews.MarkedMemoryPathEndpointData
public import ArtinMatthews.MarkedMemorySourceTilt
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The literal bandwise path choices and their actual orphan count
instantiate the finite prime-choice tail. Prime bands remain separate
typed carriers; no disjointness or coverage premise replaces this finite
currying equivalence. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)

theorem markedMemoryPathOrphanCount_uncurried
    (c : (Σ j,↥(P j)) → MarkedMemoryPrimeLifespanChoice n) :
    markedMemoryPrimeOrphanCount (fun a : Σ j,↥(P j) => markedMemoryPathVisits d a.1 a.2) c =
      markedMemoryPathOrphanCount d (Sigma.curry c) := by
  unfold markedMemoryPrimeOrphanCount markedMemoryPathOrphanCount
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  simp only [markedMemoryPathChosenOrphans,Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases ha : (markedMemoryPathVisits d j p).Nonempty <;>
    by_cases hc : c ⟨j,p⟩=(none,none) <;>
    simp only [markedMemoryPrimeOrphanCost,markedMemoryOrphanChoiceCost,ha,hc,
      ite_true,ite_false,not_true_eq_false,not_false_eq_true,false_and,true_and,
      ne_eq,not_true_eq_false,Sigma.curry]

def markedMemoryPathPrimeChoiceWeight (q : ℝ)
    (c : MarkedMemoryPathPrimeChoices (P := P) (n := n)) : ℝ :=
  ∏ j,∏ p : P j,markedMemoryPrimeLifespanChoiceWeight (markedMemoryEta q n)
    (markedMemoryPathPrimeLines hZ d p) (markedMemoryPathVisits d j p)
    (markedMemoryLineBirthAtom q n p.1) (c j p)

def markedMemoryPathActiveChoiceAbsoluteMass (q : ℝ) : ℝ :=
  ∏ j,∏ p : P j,markedMemoryPrimeActiveAbsoluteMass (markedMemoryEta q n)
    (markedMemoryPathPrimeLines hZ d p) (markedMemoryPathVisits d j p)
    (markedMemoryLineBirthAtom q n p.1)

def markedMemoryPathInactiveAtomMass (q : ℝ) : ℝ :=
  ∑ j,∑ p : P j,markedMemoryPrimeInactiveAtom (markedMemoryPathVisits d j p)
    (markedMemoryLineBirthAtom q n p.1)

theorem markedMemoryPathOrphan_absolute_tail (q : ℝ) (hq0 : 0≤q) (hq1 : q≤1)
    (ha : ∀ j (p : P j),0 ≤ markedMemoryLineBirthAtom q n p.1)
    (r : ℝ) (hr : 1≤r) (m : ℕ) :
    (∑ c : MarkedMemoryPathPrimeChoices (P := P) (n := n),
      if m ≤ markedMemoryPathOrphanCount d c then |markedMemoryPathPrimeChoiceWeight hZ d q c| else 0) ≤
      markedMemoryPathActiveChoiceAbsoluteMass hZ d q *
        Real.exp (r*markedMemoryPathInactiveAtomMass d q*((n:ℝ)+1)^2)/r^m := by
  let : DecidableEq (Σ j,↥(P j)) := Classical.decEq _
  let e := Equiv.piCurry (fun j (_p : P j) => MarkedMemoryPrimeLifespanChoice n)
  let f := fun c : MarkedMemoryPathPrimeChoices (P := P) (n := n) =>
    if m ≤ markedMemoryPathOrphanCount d c then |markedMemoryPathPrimeChoiceWeight hZ d q c| else 0
  have hs : (∑ c : MarkedMemoryPathPrimeChoices (P := P) (n := n),f c)=
      ∑ c : (Σ j,↥(P j)) → MarkedMemoryPrimeLifespanChoice n,
        if m ≤ markedMemoryPrimeOrphanCount (fun a : Σ j,↥(P j) => markedMemoryPathVisits d a.1 a.2) c then
          ∏ a : Σ j,↥(P j),|markedMemoryPrimeLifespanChoiceWeight (markedMemoryEta q n)
            (markedMemoryPathPrimeLines hZ d a.2) (markedMemoryPathVisits d a.1 a.2)
            (markedMemoryLineBirthAtom q n a.2.1) (c a)| else 0 := by
    simpa only [e,f,Equiv.piCurry_apply,markedMemoryPathOrphanCount_uncurried,
      markedMemoryPathPrimeChoiceWeight,Finset.abs_prod,Fintype.prod_sigma,Sigma.curry] using
      (Equiv.sum_comp e f).symm
  rw [show (∑ c : MarkedMemoryPathPrimeChoices (P := P) (n := n),
    if m ≤ markedMemoryPathOrphanCount d c then |markedMemoryPathPrimeChoiceWeight hZ d q c| else 0)=
      ∑ c : MarkedMemoryPathPrimeChoices (P := P) (n := n),f c from rfl,hs]
  simpa only [Fintype.prod_sigma,Fintype.sum_sigma,markedMemoryPathActiveChoiceAbsoluteMass,
    markedMemoryPathInactiveAtomMass] using
    markedMemoryPrimeOrphan_absolute_tail (I := Σ j,↥(P j)) (markedMemoryEta q n)
      (fun a : Σ j,↥(P j) => markedMemoryPathPrimeLines hZ d a.2)
      (fun a : Σ j,↥(P j) => markedMemoryPathVisits d a.1 a.2)
      (fun a : Σ j,↥(P j) => markedMemoryLineBirthAtom q n a.2.1)
      (markedMemoryEta_mem_unitInterval hq0 hq1 n) (fun a => ha a.1 a.2) r hr m

end
end ArtinMatthews
