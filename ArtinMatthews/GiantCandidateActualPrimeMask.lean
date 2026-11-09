module

public import ArtinMatthews.GiantCandidateActualResidueMask
public import ArtinMatthews.GiantCandidatePrimeResidueModel


set_option backward.privateInPublic true
@[expose] public section

/-! Product-dyad transfer for arbitrary separate residue tests at a
bounded number of the actual candidate primes. -/

namespace ArtinMatthews
noncomputable section
open Finset Filter
open scoped BigOperators

theorem giant_candidate_actual_prime_mask_eventually (τ A : ℝ)
    (hτ : 0 < τ) (hA : 0 ≤ A) (r j : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ U : Finset ℕ,U ⊆ giantCandidateFullPrimes x → U.card≤r →
      ∀ (H : Fin j → ℕ) (E : ∀ p : U,Finset (Fin j → ZMod p.val)),(∀ i,x^τ≤(H i:ℝ)) →
      let W := Real.exp ((Real.log x)^(6/25:ℝ))
      let S (i : Fin j) := giantCandidateRoughFullDyad W (H i)
      let ε := (Real.log x)^(-A)
      let μ := ((giantCandidatePrimeTupleMask S E).card:ℝ)/((Fintype.piFinset S).card:ℝ)
      let v := ∏ p : U,((E p).card:ℝ)/(p.val:ℝ)^j
      0 < (Fintype.piFinset S).card ∧ (1-ε)^j*v ≤ μ ∧ μ ≤ (1+ε)^j*v := by
  filter_upwards [giantCandidateFullPrimes_prime_upper_eventually,
    giant_candidate_actual_rough_residue_mask_eventually τ A hτ hA r j] with x hP hmask
  intro U hU hr H E hH
  have hprime : ∀p∈U,p.Prime := fun p hp => (hP p (hU hp)).1
  have h := hmask U hU hr H (giantCandidatePrimeCRTMask U hprime E) hH
  simpa only [giantCandidatePrimeCRTMask_uniformMass,giantCandidateTupleResidueMass,
    ← giantCandidatePrimeTupleMask_eq_residueMask U hprime] using h

end
end ArtinMatthews
