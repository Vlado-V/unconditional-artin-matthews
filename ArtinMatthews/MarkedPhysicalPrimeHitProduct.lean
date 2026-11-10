module

public import ArtinMatthews.MarkedPhysicalInactiveDamping
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

/-! The physical inactive-hit product over the actual union of prime
bands. Disjoint bands justify charging each prime once, with the active
ordered-label set retained at every visit. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalBandPrimes {J : Type*} [Fintype J] (P : J → Finset ℕ) : Finset ℕ :=
  Finset.univ.biUnion P

def markedPhysicalActivePrimes {J : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (a : MarkedPhysicalMarking P M) : Finset ℕ := Finset.univ.biUnion (markedPhysicalLabelSet a)

def markedPhysicalPrimeVisitFactor (active : Finset ℕ) (r : ℝ) (u p : ℕ) : ℝ :=
  if p ∈ active then 1 else if p ∣ u then r else 1

theorem markedPhysicalActivePrimes_subset {J : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (a : MarkedPhysicalMarking P M) : markedPhysicalActivePrimes a ⊆ markedPhysicalBandPrimes P := by
  intro p hp
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,markedPhysicalLabelSet_subset a j hj⟩

theorem markedPhysicalActivePrimes_mem_group {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {M : ℕ}
    (a : MarkedPhysicalMarking P M) (j : J) {p : ℕ} (hp : p ∈ P j) :
    p ∈ markedPhysicalActivePrimes a ↔ p ∈ markedPhysicalLabelSet a j := by
  constructor
  · intro h
    obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp h
    by_cases hkj : k=j
    · simpa only [hkj] using hk
    · exact (Finset.disjoint_left.mp (hdis hkj) (markedPhysicalLabelSet_subset a k hk) hp).elim
  · intro h
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,h⟩

theorem markedPhysicalInactivePrimeWeight_global {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {M : ℕ}
    (a : MarkedPhysicalMarking P M) (r : ℝ) (u : ℕ) :
    markedPhysicalInactivePrimeWeight P a r u =
      ∏ p ∈ markedPhysicalBandPrimes P,markedPhysicalPrimeVisitFactor (markedPhysicalActivePrimes a) r u p := by
  unfold markedPhysicalBandPrimes
  rw [Finset.prod_biUnion (fun i _ j _ hij => hdis hij)]
  unfold markedPhysicalInactivePrimeWeight
  apply Finset.prod_congr rfl
  intro j _
  calc
    _ = ∏ p ∈ P j,if p ∈ markedPhysicalLabelSet a j then 1 else if p ∣ u then r else 1 := by
      have he : (P j).filter (fun p => p ∉ markedPhysicalLabelSet a j) = P j \ markedPhysicalLabelSet a j := by
        ext p
        simp only [Finset.mem_filter,Finset.mem_sdiff]
      symm
      rw [Finset.prod_ite,Finset.prod_const_one,one_mul,he]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      unfold markedPhysicalPrimeVisitFactor
      simp only [markedPhysicalActivePrimes_mem_group hdis a j hp]

theorem markedPhysicalPrimeVisitFactor_mem_unitInterval (active : Finset ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (u p : ℕ) :
    0 ≤ markedPhysicalPrimeVisitFactor active r u p ∧ markedPhysicalPrimeVisitFactor active r u p ≤ 1 := by
  unfold markedPhysicalPrimeVisitFactor
  split_ifs <;> constructor <;> linarith

end ArtinMatthews
