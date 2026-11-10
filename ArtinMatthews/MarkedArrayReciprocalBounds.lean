module

public import ArtinMatthews.MarkedArrayMass
public import ArtinMatthews.MarkedArrayEulerModel
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

/-! Uniform reciprocal coefficient bounds for the actual single- and
double-array expansions, including coincident choices in a repeated band. -/

namespace ArtinMatthews

open scoped BigOperators

theorem representedArrayCoefficient_nonneg {ι : Type*} [Fintype ι]
    (V : ι → ℝ) (hV : ∀ i, 0 ≤ V i) (a : ι → ℕ)
    (t : (i : ι) → Fin (a i) → ℕ) : 0 ≤ representedArrayCoefficient V a t := by
  unfold representedArrayCoefficient
  exact div_nonneg (Finset.prod_nonneg (fun _ _ => by positivity))
    (Finset.prod_nonneg (fun i _ => pow_nonneg (hV i) _))

theorem represented_array_normalized_reciprocal_mass {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (V : ι → ℝ) (hV : ∀ i, 0 ≤ V i) (a : ι → ℕ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) :
    (∑ t ∈ representedArrayChoices P a, |representedArrayCoefficient V a t| /
      (∏ p ∈ representedArraySelected t, p : ℕ)) =
        ∏ i, representedTupleReciprocalMass (P i) (a i) (1 / 2) / (V i) ^ a i := by
  classical
  simp_rw [abs_of_nonneg (representedArrayCoefficient_nonneg V hV a _)]
  calc
    _ = (∑ t ∈ representedArrayChoices P a,
        (∏ i, (1 / 2 : ℝ) ^ (a i * ((representedChoiceSet (t i)).card - 1))) /
          (∏ p ∈ Finset.univ.biUnion (fun i => representedChoiceSet (t i)), (p : ℝ))) /
            (∏ i, (V i) ^ a i) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro t ht
      unfold representedArrayCoefficient representedArraySelected
      rw [Nat.cast_prod]
      ring
    _ = _ := by
      rw [represented_array_reciprocal_mass_factor P a (1 / 2) hdis,
        Finset.prod_div_distrib]

theorem representedTupleReciprocalMass_nonneg (P : Finset ℕ) (a : ℕ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) : 0 ≤ representedTupleReciprocalMass P a ρ := by
  unfold representedTupleReciprocalMass
  exact Finset.sum_nonneg (fun _ _ => div_nonneg (pow_nonneg hρ _)
    (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p)))

/-- The bound is independent of the sizes and locations of the prime
bands. Only their number and a common positive reciprocal-mass bound enter. -/
theorem represented_array_reciprocal_mass_uniform {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (a : ι → ℕ) (ha : ∀ i, a i = 1 ∨ a i = 2)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    {v : ℝ} (hv : 0 < v) (hV : ∀ i, v ≤ bandReciprocalMass (P i)) :
    (∑ t ∈ representedArrayChoices P a,
      |representedArrayCoefficient (fun i => bandReciprocalMass (P i)) a t| /
        (∏ p ∈ representedArraySelected t, p : ℕ)) ≤
          (max 1 (1 / v + 1 / 4)) ^ Fintype.card ι := by
  have hpos : ∀ i, 0 < bandReciprocalMass (P i) := fun i => hv.trans_le (hV i)
  rw [represented_array_normalized_reciprocal_mass P _ (fun i => (hpos i).le) a hdis]
  calc
    _ ≤ ∏ _i : ι, (max 1 (1 / v + 1 / 4)) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact div_nonneg (representedTupleReciprocalMass_nonneg _ _ (by norm_num))
          (pow_nonneg (hpos i).le _)
      · intro i hi
        rcases ha i with hi | hi
        · rw [hi, representedTupleReciprocalMass_one, pow_one, div_self (hpos i).ne']
          exact le_max_left _ _
        · rw [hi, representedTupleReciprocalMass_two]
          have h := representedPairReciprocalMass_normalized_le (P i) (1 / 2) hv (hV i)
          norm_num at h
          exact h.trans (by simpa only [one_div] using (le_max_right (1 : ℝ) (1 / v + 1 / 4)))
    _ = _ := by simp

end ArtinMatthews
