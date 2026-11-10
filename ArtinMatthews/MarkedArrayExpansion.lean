module

public import ArtinMatthews.MarkedArrayResidual
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

/-! The represented-prime expansion of actual marking weights, with all
ordered tuples retained even when their selected primes coincide. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable def representedChoiceSet {a : ℕ} (t : Fin a → ℕ) : Finset ℕ :=
  Finset.univ.image t

theorem representedChoiceSet_subset {a : ℕ} {P : Finset ℕ} {t : Fin a → ℕ}
    (ht : ∀ j, t j ∈ P) : representedChoiceSet t ⊆ P := by
  intro p hp
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
  exact ht j

theorem representedChoiceSet_active_iff {a : ℕ} {P : Finset ℕ} {t : Fin a → ℕ}
    (ht : ∀ j, t j ∈ P) (u : ℕ) :
    representedChoiceSet t ⊆ activeDivisors P u ↔ ∀ j, t j ∣ u := by
  classical
  constructor
  · intro h j
    exact (Finset.mem_filter.mp (h (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩))).2
  · intro h p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨ht j, h j⟩

theorem representedChoiceSet_nonempty {a : ℕ} (ha : 0 < a) (t : Fin a → ℕ) :
    (representedChoiceSet t).Nonempty :=
  ⟨t ⟨0, ha⟩, Finset.mem_image.mpr ⟨⟨0, ha⟩, Finset.mem_univ _, rfl⟩⟩

theorem representedBandTerm_eq_tuple_product {a : ℕ} (ha : 0 < a)
    (P : Finset ℕ) (t : Fin a → ℕ) (ht : ∀ j, t j ∈ P) (u : ℕ) (ρ : ℝ) :
    representedBandTerm P (representedChoiceSet t) u a ρ =
      ∏ j : Fin a, if t j ∣ u then ρ ^ (bandCount P u - 1) else 0 := by
  classical
  by_cases hdiv : ∀ j, t j ∣ u
  · rw [representedBandTerm_eq_of_subset
      ((representedChoiceSet_active_iff ht u).mpr hdiv)
      (representedChoiceSet_nonempty ha t)]
    simp only [hdiv, ite_eq_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul, Nat.mul_comm]
  · rw [representedBandTerm, ite_eq_right (fun h => hdiv
      ((representedChoiceSet_active_iff ht u).mp h))]
    push Not at hdiv
    obtain ⟨j, hj⟩ := hdiv
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

/-- Every positive power of a band weight has an exact ordered-tuple
expansion. In particular `a=2` retains the diagonal tuples rather than
silently replacing them by two-element sets. -/
theorem bandWeight_pow_eq_represented_tuple_sum (P : Finset ℕ) (V : ℝ) (u a : ℕ)
    (ha : 0 < a) :
    (bandWeight P V u) ^ a =
      (∑ t ∈ Fintype.piFinset (fun _ : Fin a => P),
        representedBandTerm P (representedChoiceSet t) u a (1 / 2)) / V ^ a := by
  classical
  have hs : (∑ p ∈ P, if p ∣ u then (1 / 2 : ℝ) ^ (bandCount P u - 1) else 0) =
      halfDampedCount (bandCount P u) := by
    rw [← Finset.sum_filter]
    simp [halfDampedCount, activeDivisors, bandCount]
  have ht := Finset.prod_univ_sum (fun _ : Fin a => P)
    (fun _ p => if p ∣ u then (1 / 2 : ℝ) ^ (bandCount P u - 1) else 0)
  have heq : (halfDampedCount (bandCount P u)) ^ a =
      ∑ t ∈ Fintype.piFinset (fun _ : Fin a => P),
        representedBandTerm P (representedChoiceSet t) u a (1 / 2) := by
    rw [← hs]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at ht
    rw [ht]
    apply Finset.sum_congr rfl
    intro t htm
    exact (representedBandTerm_eq_tuple_product ha P t
      (Fintype.mem_piFinset.mp htm) u (1 / 2)).symm
  rw [bandWeight, div_pow, heq]

/-- The actual ordered selections for a family of marking bands. -/
noncomputable def representedArrayChoices {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (a : ι → ℕ) : Finset ((i : ι) → Fin (a i) → ℕ) := by
  classical
  exact Fintype.piFinset (fun i => Fintype.piFinset (fun _ : Fin (a i) => P i))

/-- Full multi-band expansion with one residual on the union of primes.
The normalizing factors and tuple multiplicities are kept exactly. -/
theorem bandWeight_product_powers_eq_union_residual_sum {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (V : ι → ℝ) (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) (u : ℕ) :
    (∏ i, (bandWeight (P i) (V i) u) ^ a i) =
      (∑ t ∈ representedArrayChoices P a,
        (∏ i, (1 / 2 : ℝ) ^ (a i * ((representedChoiceSet (t i)).card - 1))) *
          markedWeightedResidual (Finset.univ.biUnion P)
            (Finset.univ.biUnion (fun i => representedChoiceSet (t i)))
            (representedArrayDamping Finset.univ P a (1 / 2)) u) /
        (∏ i, (V i) ^ a i) := by
  classical
  have hweights : (∏ i, (bandWeight (P i) (V i) u) ^ a i) =
      (∏ i, ∑ t ∈ Fintype.piFinset (fun _ : Fin (a i) => P i),
        representedBandTerm (P i) (representedChoiceSet t) u (a i) (1 / 2)) /
          ∏ i, (V i) ^ a i := by
    rw [← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl (fun i _ =>
      bandWeight_pow_eq_represented_tuple_sum (P i) (V i) u (a i) (ha i))
  rw [hweights]
  congr 1
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have htp : ∀ i j, t i j ∈ P i := fun i =>
    Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp ht i)
  exact represented_bands_eq_union_residual Finset.univ P
    (fun i => representedChoiceSet (t i)) a (1 / 2)
    (fun i _ j _ hij => hdis hij)
    (fun i _ => representedChoiceSet_subset (htp i)) u

end ArtinMatthews
