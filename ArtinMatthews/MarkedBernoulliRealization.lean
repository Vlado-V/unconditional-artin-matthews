module

public import ArtinMatthews.MarkedArrayExpansion
public import ArtinMatthews.MarkedProgressionBernoulli
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

/-! Every mask of a finite set of primes is realized by the product of
its elements. This identifies the represented Euler main term with the
actual independent Bernoulli moments of the marking weights. -/

namespace ArtinMatthews

open scoped BigOperators

theorem prime_dvd_mask_product_iff (P A : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hA : A ⊆ P) {p : ℕ} (hp : p ∈ P) :
    p ∣ (∏ q ∈ A, q) ↔ p ∈ A := by
  constructor
  · intro hd
    obtain ⟨q, hq, hpq⟩ := (Nat.prime_iff.mp (hP p hp)).dvd_finsetProd_iff id |>.mp hd
    have heq := (Nat.prime_dvd_prime_iff_eq (hP p hp) (hP q (hA hq))).mp hpq
    exact heq ▸ hq
  · exact fun hpA => Finset.dvd_prod_of_mem id hpA

theorem activeDivisors_mask_product (P A : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hA : A ⊆ P) : activeDivisors P (∏ q ∈ A, q) = A := by
  ext p
  simp only [activeDivisors, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hd⟩
    exact (prime_dvd_mask_product_iff P A hP hA hp).mp hd
  · intro hp
    exact ⟨hA hp, (prime_dvd_mask_product_iff P A hP hA (hA hp)).mpr hp⟩

theorem markedWeightedResidual_mask_product (P S A : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P) (θ : ℕ → ℝ) :
    markedWeightedResidual P S θ (∏ q ∈ A, q) =
      markedSelectedBernoulliMask P S θ A := by
  classical
  unfold markedWeightedResidual markedSelectedBernoulliMask
  rw [activeDivisors_mask_product P A hP hA]
  split_ifs
  · apply Finset.prod_congr rfl
    intro p hp
    simp only [markedWeightedInput, prime_dvd_mask_product_iff P A hP hA (Finset.mem_sdiff.mp hp).1]
  · rfl

theorem represented_mask_power_expansion (P A : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P) (V : ℝ) (a : ℕ) (ha : 0 < a) :
    (halfDampedCount A.card / V) ^ a =
      (∑ t ∈ Fintype.piFinset (fun _ : Fin a => P),
        (1 / 2 : ℝ) ^ (a * ((representedChoiceSet t).card - 1)) *
          markedSelectedBernoulliMask P (representedChoiceSet t)
            (fun _ => 1 - (1 / 2 : ℝ) ^ a) A) / V ^ a := by
  have h := bandWeight_pow_eq_represented_tuple_sum P V (∏ q ∈ A, q) a ha
  have hw : bandWeight P V (∏ q ∈ A, q) = halfDampedCount A.card / V := by
    rw [bandWeight, bandCount, activeDivisors_mask_product P A hP hA]
  rw [hw] at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [representedBandTerm_eq_weightedResidual P (representedChoiceSet t)
    (∏ q ∈ A, q) a (1 / 2) (fun _ => 1 - (1 / 2 : ℝ) ^ a) (fun _ _ => rfl),
    markedWeightedResidual_mask_product P (representedChoiceSet t) A hP hA]

/-- The local represented Euler main term is exactly the `a`-th moment
of the finite independent band weight, with its original normalizer. -/
theorem represented_band_euler_eq_bernoulli_power (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (V : ℝ) (a : ℕ) (ha : 0 < a) :
    (∑ t ∈ Fintype.piFinset (fun _ : Fin a => P),
      (1 / 2 : ℝ) ^ (a * ((representedChoiceSet t).card - 1)) *
        markedWeightedModel P (representedChoiceSet t)
          (fun _ => 1 - (1 / 2 : ℝ) ^ a)) / V ^ a =
      ∑ A ∈ P.powerset, (halfDampedCount A.card / V) ^ a *
        bernoulliMaskMass P (fun p => 1 / (p : ℝ)) A := by
  classical
  have hpoint (t : Fin a → ℕ) (ht : t ∈ Fintype.piFinset (fun _ : Fin a => P)) :=
    marked_selected_bernoulli_expectation_eq_model P (representedChoiceSet t)
      (representedChoiceSet_subset (Fintype.mem_piFinset.mp ht))
      (fun _ => 1 - (1 / 2 : ℝ) ^ a)
  calc
    _ = (∑ t ∈ Fintype.piFinset (fun _ : Fin a => P), ∑ A ∈ P.powerset,
        ((1 / 2 : ℝ) ^ (a * ((representedChoiceSet t).card - 1)) *
          markedSelectedBernoulliMask P (representedChoiceSet t)
            (fun _ => 1 - (1 / 2 : ℝ) ^ a) A) *
              bernoulliMaskMass P (fun p => 1 / (p : ℝ)) A) / V ^ a := by
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      rw [← hpoint t ht, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      ring
    _ = ∑ A ∈ P.powerset,
        ((∑ t ∈ Fintype.piFinset (fun _ : Fin a => P),
          (1 / 2 : ℝ) ^ (a * ((representedChoiceSet t).card - 1)) *
            markedSelectedBernoulliMask P (representedChoiceSet t)
              (fun _ => 1 - (1 / 2 : ℝ) ^ a) A) / V ^ a) *
                bernoulliMaskMass P (fun p => 1 / (p : ℝ)) A := by
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro A hA
      rw [← Finset.sum_mul]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [← represented_mask_power_expansion P A hP (Finset.mem_powerset.mp hA) V a ha]

end ArtinMatthews
