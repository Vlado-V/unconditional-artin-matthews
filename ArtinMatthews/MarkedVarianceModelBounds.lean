module

public import ArtinMatthews.MarkedEstimateActualModel


set_option backward.privateInPublic true
@[expose] public section

/-! Positivity and the uniform size bound of the exact independent model
used as the main mass in the positive prime sieve. -/

namespace ArtinMatthews

open Filter
open scoped BigOperators

theorem independentArrayMass_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → Finset ℕ) (hP : ∀ i p, p ∈ P i → p.Prime) (A : ArrayMasks P) :
    0 ≤ independentArrayMass P A := by
  unfold independentArrayMass
  apply Finset.prod_nonneg
  intro i _
  exact bernoulliMaskMass_nonneg (P i) _ (primeReciprocal_probabilities (P i) (hP i))
    (Finset.mem_powerset.mp (A i).property)

theorem independentArraysVariance_nonneg {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (P : J → I → Finset ℕ) (V : J → I → ℝ)
    (hP : ∀ j i p, p ∈ P j i → p.Prime) : 0 ≤ independentArraysVariance P V := by
  unfold independentArraysVariance
  apply Finset.sum_nonneg
  intro A _
  apply mul_nonneg (sq_nonneg _)
  unfold finiteProductMass
  exact Finset.prod_nonneg (fun j _ => independentArrayMass_nonneg (P j) (hP j) (A j))

theorem marked_actual_variance_model_bounds {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (e : J → I → ℝ) (he : ∀ j i, 0 < e j i)
    (hinj : Function.Injective (fun ji : J × I => e ji.1 ji.2))
    (hJ : 0 < Fintype.card J) :
    ∀ᶠ x : ℝ in atTop,
      0 ≤ independentArraysVariance (fun j i => markedLogPowerBand (e j i) x)
        (fun j i => bandReciprocalMass (markedLogPowerBand (e j i) x)) ∧
      independentArraysVariance (fun j i => markedLogPowerBand (e j i) x)
        (fun j i => bandReciprocalMass (markedLogPowerBand (e j i) x)) ≤
          markedArrayVarianceConstant (Fintype.card I) / Fintype.card J := by
  filter_upwards [marked_arrays_variance_eventually e he hinj hJ] with x hx
  exact ⟨independentArraysVariance_nonneg _ _ (fun _ _ _ hp => (mem_markedLogPowerBand.mp hp).1), hx.2⟩

end ArtinMatthews
