module

public import ArtinMatthews.DivisorWeights
public import ArtinMatthews.MarkedProgressionWeightedModel
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! Identification of selected weighted residuals with their actual finite
independent Bernoulli model. The identities are polynomial identities in
the parameters; no positivity or probability assumptions are required. -/

namespace ArtinMatthews

open scoped BigOperators

section FiniteModel

variable {α : Type*} [DecidableEq α]

/-- A product of one-coordinate tests has the expected product mean under
the exact finite Bernoulli mask masses. -/
theorem bernoulli_mask_product_expectation (P : Finset α) (r a b : α → ℝ) :
    (∑ A ∈ P.powerset, bernoulliMaskMass P r A *
      ∏ p ∈ P, if p ∈ A then a p else b p) =
      ∏ p ∈ P, (r p * a p + (1 - r p) * b p) := by
  classical
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro A hA
  have hAP : A ⊆ P := Finset.mem_powerset.mp hA
  have hprod : (∏ p ∈ P, if p ∈ A then a p else b p) =
      (∏ p ∈ A, a p) * ∏ p ∈ P \ A, b p := by
    simpa only [Finset.piecewise, Finset.inter_eq_right.mpr hAP] using
      Finset.prod_piecewise P A a b
  rw [hprod]
  unfold bernoulliMaskMass
  simp only [Finset.prod_mul_distrib]
  ring

/-- A mask is retained precisely when it contains the selected prime set.
The remaining coordinates carry their individual damping factors. -/
noncomputable def markedSelectedBernoulliMask (P S : Finset α) (θ : α → ℝ)
    (A : Finset α) : ℝ :=
  if S ⊆ A then ∏ p ∈ P \ S, (1 - θ p * (if p ∈ A then 1 else 0)) else 0

/-- The selected-mask test is a product of local coordinate tests. -/
theorem markedSelectedBernoulliMask_eq_product (P S A : Finset α)
    (hS : S ⊆ P) (θ : α → ℝ) :
    markedSelectedBernoulliMask P S θ A =
      ∏ p ∈ P, if p ∈ A then (if p ∈ S then 1 else 1 - θ p)
        else (if p ∈ S then 0 else 1) := by
  classical
  have hind : (∏ p ∈ S, if p ∈ A then (1 : ℝ) else 0) =
      if S ⊆ A then 1 else 0 := by
    rw [Finset.prod_ite_zero]
    simp only [Finset.prod_const_one, Finset.subset_iff]
  symm
  calc
    _ = ∏ p ∈ P, if p ∈ S then (if p ∈ A then (1 : ℝ) else 0)
        else (1 - θ p * (if p ∈ A then 1 else 0)) := by
      apply Finset.prod_congr rfl
      intro p _
      by_cases hpS : p ∈ S <;> by_cases hpA : p ∈ A <;> simp [hpS, hpA]
    _ = (∏ p ∈ S, if p ∈ A then (1 : ℝ) else 0) *
        ∏ p ∈ P \ S, (1 - θ p * (if p ∈ A then 1 else 0)) := by
      simpa only [Finset.piecewise, Finset.inter_eq_right.mpr hS] using
        Finset.prod_piecewise P S (fun p => if p ∈ A then (1 : ℝ) else 0)
          (fun p => 1 - θ p * (if p ∈ A then 1 else 0))
    _ = markedSelectedBernoulliMask P S θ A := by
      rw [hind]
      unfold markedSelectedBernoulliMask
      by_cases hSA : S ⊆ A <;> simp [hSA]

/-- Exact finite independent expectation of a selected weighted residual. -/
theorem marked_selected_bernoulli_expectation (P S : Finset α) (hS : S ⊆ P)
    (r θ : α → ℝ) :
    (∑ A ∈ P.powerset,
      markedSelectedBernoulliMask P S θ A * bernoulliMaskMass P r A) =
      (∏ p ∈ S, r p) * ∏ p ∈ P \ S, (1 - θ p * r p) := by
  classical
  calc
    _ = ∑ A ∈ P.powerset, bernoulliMaskMass P r A *
        ∏ p ∈ P, if p ∈ A then (if p ∈ S then 1 else 1 - θ p)
          else (if p ∈ S then 0 else 1) := by
      apply Finset.sum_congr rfl
      intro A _
      rw [markedSelectedBernoulliMask_eq_product P S A hS θ, mul_comm]
    _ = ∏ p ∈ P, (r p * (if p ∈ S then 1 else 1 - θ p) +
        (1 - r p) * (if p ∈ S then 0 else 1)) :=
      bernoulli_mask_product_expectation P r _ _
    _ = ∏ p ∈ P, if p ∈ S then r p else 1 - θ p * r p := by
      apply Finset.prod_congr rfl
      intro p _
      by_cases hp : p ∈ S
      · simp [hp]
      · simp [hp]
        ring
    _ = _ := by
      simpa only [Finset.piecewise, Finset.inter_eq_right.mpr hS] using
        Finset.prod_piecewise P S r (fun p => 1 - θ p * r p)

end FiniteModel

/-- Reciprocal prime probabilities produce the exact selected Euler model.
Primality is not needed for this algebraic specialization. -/
theorem marked_selected_prime_bernoulli_expectation (P S : Finset ℕ)
    (hS : S ⊆ P) (θ : ℕ → ℝ) :
    (∑ A ∈ P.powerset, markedSelectedBernoulliMask P S θ A *
      bernoulliMaskMass P (fun p => 1 / (p : ℝ)) A) =
      (1 / (∏ p ∈ S, p : ℕ)) * ∏ p ∈ P \ S, (1 - θ p / (p : ℝ)) := by
  rw [marked_selected_bernoulli_expectation P S hS]
  simp only [Nat.cast_prod, div_eq_mul_inv, one_mul, Finset.prod_inv_distrib]

/-- The finite independent divisor model is exactly the Euler model used
in the selected weighted progression estimate. -/
theorem marked_selected_bernoulli_expectation_eq_model (P S : Finset ℕ)
    (hS : S ⊆ P) (θ : ℕ → ℝ) :
    (∑ A ∈ P.powerset, markedSelectedBernoulliMask P S θ A *
      bernoulliMaskMass P (fun p => 1 / (p : ℝ)) A) =
      markedWeightedModel P S θ :=
  marked_selected_prime_bernoulli_expectation P S hS θ

end ArtinMatthews
