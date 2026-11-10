module

public import ArtinMatthews.MarkedArrayExpansion
public import ArtinMatthews.MarkedRepresentedMass
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Reciprocal masses of represented unions factor across genuinely
disjoint bands, with repeated selections kept as ordered tuples. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable def representedTupleReciprocalMass (P : Finset ℕ) (a : ℕ) (ρ : ℝ) : ℝ :=
  ∑ t ∈ Fintype.piFinset (fun _ : Fin a => P),
    ρ ^ (a * ((representedChoiceSet t).card - 1)) /
      ∏ p ∈ representedChoiceSet t, (p : ℝ)

theorem represented_union_reciprocal_eq_product {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (a : ι → ℕ) (ρ : ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (t : (i : ι) → Fin (a i) → ℕ) (ht : t ∈ representedArrayChoices P a) :
    (∏ i, ρ ^ (a i * ((representedChoiceSet (t i)).card - 1))) /
        (∏ p ∈ Finset.univ.biUnion (fun i => representedChoiceSet (t i)), (p : ℝ)) =
      ∏ i, ρ ^ (a i * ((representedChoiceSet (t i)).card - 1)) /
        (∏ p ∈ representedChoiceSet (t i), (p : ℝ)) := by
  classical
  have htp : ∀ i j, t i j ∈ P i := fun i =>
    Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp ht i)
  have hpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι))
      (fun i => representedChoiceSet (t i)) := by
    intro i _ j _ hij
    exact (hdis hij).mono (representedChoiceSet_subset (htp i))
      (representedChoiceSet_subset (htp j))
  rw [Finset.prod_biUnion hpair, Finset.prod_div_distrib]

/-- Exact factorization of the mass multiplying the Bonferroni tail and
the local coprimality loss in the actual array expansion. -/
theorem represented_array_reciprocal_mass_factor {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (a : ι → ℕ) (ρ : ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) :
    (∑ t ∈ representedArrayChoices P a,
      (∏ i, ρ ^ (a i * ((representedChoiceSet (t i)).card - 1))) /
        (∏ p ∈ Finset.univ.biUnion (fun i => representedChoiceSet (t i)), (p : ℝ))) =
      ∏ i, representedTupleReciprocalMass (P i) (a i) ρ := by
  classical
  simp_rw [representedTupleReciprocalMass]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact represented_union_reciprocal_eq_product P a ρ hdis t ht

theorem representedChoiceSet_one (t : Fin 1 → ℕ) :
    representedChoiceSet t = {t 0} := by
  ext p
  simp [representedChoiceSet]

theorem representedTupleReciprocalMass_one (P : Finset ℕ) (ρ : ℝ) :
    representedTupleReciprocalMass P 1 ρ = bandReciprocalMass P := by
  classical
  unfold representedTupleReciprocalMass bandReciprocalMass
  apply Finset.sum_bij (fun t _ => t 0)
  · intro t ht
    exact Fintype.mem_piFinset.mp ht 0
  · intro t ht s hs hts
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    simpa [hj] using hts
  · intro p hp
    exact ⟨fun _ => p, Fintype.mem_piFinset.mpr (fun _ => hp), rfl⟩
  · intro t ht
    simp [representedChoiceSet_one]

theorem representedChoiceSet_two (t : Fin 2 → ℕ) :
    representedChoiceSet t = {t 0, t 1} := by
  ext p
  simp [representedChoiceSet, Fin.exists_fin_two, eq_comm]

theorem representedTupleReciprocalMass_two (P : Finset ℕ) (ρ : ℝ) :
    representedTupleReciprocalMass P 2 ρ = representedPairReciprocalMass P ρ := by
  classical
  unfold representedTupleReciprocalMass representedPairReciprocalMass
  rw [← Finset.sum_product (f := fun pq : ℕ × ℕ =>
    ρ ^ (2 * (({pq.1, pq.2} : Finset ℕ).card - 1)) /
      ∏ r ∈ ({pq.1, pq.2} : Finset ℕ), (r : ℝ))]
  apply Finset.sum_bij (fun t _ => (t 0, t 1))
  · intro t ht
    exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mp ht 0, Fintype.mem_piFinset.mp ht 1⟩
  · intro t ht s hs hts
    funext j
    fin_cases j
    · exact congrArg Prod.fst hts
    · exact congrArg Prod.snd hts
  · intro pq hpq
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
    refine ⟨![pq.1, pq.2], Fintype.mem_piFinset.mpr ?_, ?_⟩
    · intro j
      fin_cases j <;> assumption
    · rfl
  · intro t ht
    simp only [representedChoiceSet_two]

end ArtinMatthews
