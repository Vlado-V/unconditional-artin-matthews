module

public import ArtinMatthews.GiantCandidateFullResidueModel
public import ArtinMatthews.GiantCandidatePrimeHitProbabilities
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
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

/-! At each independent model prime the predecessor, product, and
neither-hit events are literal disjoint finite residue masks. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

theorem giantCandidateModelPrime_prime {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (p : giantCandidateSelectionPrimes G) :
    p.val.Prime := by
  obtain ⟨i,hi⟩ := mem_giantCandidateSelectionPrimes.mp p.property
  exact hG i p.val hi

def giantCandidateModelHitCoordinate {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) (p : giantCandidateSelectionPrimes G)
    (side : GiantCandidateHitSide) : Finset (Fin j → ZMod p.val) :=
  (giantCandidateModelPrimeCoordinate G hG j p).filter (giantCandidatePrimeResidueHit side)

def giantCandidateModelNoHitCoordinate {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) (p : giantCandidateSelectionPrimes G) :
    Finset (Fin j → ZMod p.val) :=
  (giantCandidateModelPrimeCoordinate G hG j p).filter
    (fun t => ¬giantCandidatePrimeResidueHit .predecessor t ∧ ¬giantCandidatePrimeResidueHit .product t)

theorem mem_giantCandidateModelHitCoordinate {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) (p : giantCandidateSelectionPrimes G)
    (side : GiantCandidateHitSide) (t : Fin j → ZMod p.val) :
    t∈giantCandidateModelHitCoordinate G hG j p side ↔ giantCandidatePrimeResidueHit side t := by
  rw [giantCandidateModelHitCoordinate,mem_filter]
  exact and_iff_right (giantCandidateModelPrimeCoordinate_mem G hG j p t)

theorem mem_giantCandidateModelNoHitCoordinate {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) (p : giantCandidateSelectionPrimes G)
    (t : Fin j → ZMod p.val) :
    t∈giantCandidateModelNoHitCoordinate G hG j p ↔
      ¬giantCandidatePrimeResidueHit .predecessor t ∧ ¬giantCandidatePrimeResidueHit .product t := by
  rw [giantCandidateModelNoHitCoordinate,mem_filter]
  exact and_iff_right (giantCandidateModelPrimeCoordinate_mem G hG j p t)

def giantCandidateModelHitAtom {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) (p : giantCandidateSelectionPrimes G)
    (side : GiantCandidateHitSide) : ℝ :=
  ((giantCandidateModelHitCoordinate G hG j p side).card:ℝ)/(p.val:ℝ)^j

def giantCandidateModelNoHitAtom {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) (p : giantCandidateSelectionPrimes G) : ℝ :=
  ((giantCandidateModelNoHitCoordinate G hG j p).card:ℝ)/(p.val:ℝ)^j

theorem giantCandidateModelHitAtom_eq {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) (p : giantCandidateSelectionPrimes G)
    [NeZero p.val] (side : GiantCandidateHitSide) :
    giantCandidateModelHitAtom G hG j p side = giantCandidatePrimeHitProbability p.val j side := by
  unfold giantCandidateModelHitAtom giantCandidatePrimeHitProbability
  congr 2

theorem giantCandidateModelNoHitAtom_eq {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) (p : giantCandidateSelectionPrimes G) :
    giantCandidateModelNoHitAtom G hG j p =
      1-giantCandidateModelHitAtom G hG j p .predecessor-
        giantCandidateModelHitAtom G hG j p .product := by
  let _ : Fact p.val.Prime := ⟨giantCandidateModelPrime_prime G hG p⟩
  let S := giantCandidateModelPrimeCoordinate G hG j p
  let A := giantCandidateModelHitCoordinate G hG j p .predecessor
  let B := giantCandidateModelHitCoordinate G hG j p .product
  let N := giantCandidateModelNoHitCoordinate G hG j p
  have hd : Disjoint A B := by
    apply disjoint_left.mpr
    intro t ha hb
    have h₁ := (mem_giantCandidateModelHitCoordinate G hG j p .predecessor t).mp ha
    have h₂ := (mem_giantCandidateModelHitCoordinate G hG j p .product t).mp hb
    exact one_ne_zero (h₁.symm.trans h₂)
  have hs : A∪B⊆S := union_subset (filter_subset _ _) (filter_subset _ _)
  have hN : N = S \ (A∪B) := by
    ext t
    simp only [N,A,B,mem_giantCandidateModelNoHitCoordinate,mem_sdiff,mem_union,
      mem_giantCandidateModelHitCoordinate]
    exact ⟨fun h => ⟨giantCandidateModelPrimeCoordinate_mem G hG j p t,fun ht => ht.elim h.1 h.2⟩,
      fun h => ⟨fun hh => h.2 (Or.inl hh),fun hh => h.2 (Or.inr hh)⟩⟩
  have hcount := card_le_card hs
  rw [card_union_of_disjoint hd] at hcount
  have hden : (p.val:ℝ)^j≠0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (giantCandidateModelPrime_prime G hG p).ne_zero)
  change (N.card:ℝ)/(p.val:ℝ)^j = 1-(A.card:ℝ)/(p.val:ℝ)^j-(B.card:ℝ)/(p.val:ℝ)^j
  rw [hN,card_sdiff_of_subset hs,card_union_of_disjoint hd,Nat.cast_sub hcount,Nat.cast_add,
    giantCandidateModelPrimeCoordinate_card,Nat.cast_pow,sub_div,div_self hden,add_div]
  ring

theorem giantCandidateModelNoHitAtom_mem_unitInterval {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) (p : giantCandidateSelectionPrimes G) :
    giantCandidateModelNoHitAtom G hG j p∈Set.Icc (0:ℝ) 1 := by
  unfold giantCandidateModelNoHitAtom
  refine ⟨by positivity,?_⟩
  apply (div_le_one (pow_pos (Nat.cast_pos.mpr (giantCandidateModelPrime_prime G hG p).pos) _)).mpr
  have hs : ((giantCandidateModelNoHitCoordinate G hG j p).card:ℝ) ≤
      ((giantCandidateModelPrimeCoordinate G hG j p).card:ℝ) :=
    Nat.cast_le.mpr (card_le_card (filter_subset _ _))
  rw [giantCandidateModelPrimeCoordinate_card,Nat.cast_pow] at hs
  exact hs

end
end ArtinMatthews
