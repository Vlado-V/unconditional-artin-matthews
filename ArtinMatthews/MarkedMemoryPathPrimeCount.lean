module

public import ArtinMatthews.MarkedMemoryActivePathData
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
public import Mathlib.Tactic.Basify
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

/-! Actual used-prime counts: the active occurrence image plus genuinely
chosen orphan primes. The full prime-band cardinality is not a cutoff. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n : ℕ} {Z : Finset (ℤ × ℤ)}
  (d : MarkedMemoryActivePathData P pads Z n)

def markedMemoryPathActivePrimes (j : J) : Finset (P j) :=
  Finset.univ.image (fun vk : Fin (n+1) × Fin (pads+1) => d.active vk.1 j vk.2)

omit [Fintype J] in
theorem mem_markedMemoryPathActivePrimes (j : J) (p : P j) :
    p∈markedMemoryPathActivePrimes d j ↔ (markedMemoryPathVisits d j p).Nonempty := by
  constructor
  · intro h
    obtain ⟨⟨v,k⟩,_,hk⟩ := Finset.mem_image.mp h
    exact ⟨v,(markedMemoryPathVisits_mem d j p v).mpr ⟨k,hk⟩⟩
  · rintro ⟨v,hv⟩
    obtain ⟨k,hk⟩ := (markedMemoryPathVisits_mem d j p v).mp hv
    exact Finset.mem_image.mpr ⟨(v,k),Finset.mem_univ _,hk⟩

omit [Fintype J] in
theorem markedMemoryPathActivePrimes_card_le (j : J) :
    (markedMemoryPathActivePrimes d j).card≤(n+1)*(pads+1) := by
  have h := Finset.card_image_le (s := Finset.univ)
    (f := fun vk : Fin (n+1) × Fin (pads+1) => d.active vk.1 j vk.2)
  simpa only [markedMemoryPathActivePrimes,Finset.card_univ,Fintype.card_prod,Fintype.card_fin] using h

variable (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))

def markedMemoryPathChosenOrphans (j : J) : Finset (P j) :=
  Finset.univ.filter (fun p => ¬(markedMemoryPathVisits d j p).Nonempty ∧ c j p≠(none,none))

omit [Fintype J] in
theorem mem_markedMemoryPathChosenOrphans (j : J) (p : P j) :
    p∈markedMemoryPathChosenOrphans d c j ↔
      ¬(markedMemoryPathVisits d j p).Nonempty ∧ c j p≠(none,none) := by
  simp only [markedMemoryPathChosenOrphans,Finset.mem_filter,Finset.mem_univ,true_and]

def markedMemoryPathUsedPrimes (j : J) : Finset (P j) :=
  Finset.univ.filter (fun p => MarkedMemoryPrimeLifespanUsed (markedMemoryPathVisits d j p) (c j p))

omit [Fintype J] in
theorem mem_markedMemoryPathUsedPrimes (j : J) (p : P j) :
    p∈markedMemoryPathUsedPrimes d c j ↔
      MarkedMemoryPrimeLifespanUsed (markedMemoryPathVisits d j p) (c j p) :=
  Finset.mem_filter_univ p

omit [Fintype J] in
theorem markedMemoryPathUsedPrimes_eq_union (j : J) :
    markedMemoryPathUsedPrimes d c j =
      markedMemoryPathActivePrimes d j ∪ markedMemoryPathChosenOrphans d c j := by
  apply Finset.ext
  intro p
  rw [Finset.mem_union,mem_markedMemoryPathUsedPrimes,mem_markedMemoryPathActivePrimes,
    mem_markedMemoryPathChosenOrphans]
  unfold MarkedMemoryPrimeLifespanUsed
  tauto

omit [Fintype J] in
theorem markedMemoryPathActivePrimes_disjoint_orphans (j : J) :
    Disjoint (markedMemoryPathActivePrimes d j) (markedMemoryPathChosenOrphans d c j) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact (mem_markedMemoryPathChosenOrphans d c j p).mp hq |>.1
    ((mem_markedMemoryPathActivePrimes d j p).mp hp)

omit [Fintype J] in
theorem markedMemoryPathUsedPrime_card (j : J) :
    Fintype.card (MarkedMemoryPathUsedPrime d c j) =
      (markedMemoryPathActivePrimes d j).card+(markedMemoryPathChosenOrphans d c j).card := by
  rw [Fintype.card_subtype]
  change (markedMemoryPathUsedPrimes d c j).card=_
  rw [markedMemoryPathUsedPrimes_eq_union,
    Finset.card_union_of_disjoint (markedMemoryPathActivePrimes_disjoint_orphans d c j)]

omit [Fintype J] in
theorem markedMemoryPathUsedPrime_card_le (j : J) :
    Fintype.card (MarkedMemoryPathUsedPrime d c j)≤
      (n+1)*(pads+1)+(markedMemoryPathChosenOrphans d c j).card := by
  rw [markedMemoryPathUsedPrime_card]
  exact Nat.add_le_add_right (markedMemoryPathActivePrimes_card_le d j) _

def markedMemoryPathOrphanCount : ℕ := ∑ j,(markedMemoryPathChosenOrphans d c j).card

theorem markedMemoryPathUsedPrime_total_card_le :
    (∑ j,Fintype.card (MarkedMemoryPathUsedPrime d c j))≤
      Fintype.card J*((n+1)*(pads+1))+markedMemoryPathOrphanCount d c := by
  calc
    _ ≤ ∑ j,((n+1)*(pads+1)+(markedMemoryPathChosenOrphans d c j).card) :=
      Finset.sum_le_sum (fun j _ => markedMemoryPathUsedPrime_card_le d c j)
    _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,Nat.cast_id,markedMemoryPathOrphanCount]

end
end ArtinMatthews
