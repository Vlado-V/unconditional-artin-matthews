module

public import ArtinMatthews.GiantSourceResidueCost
public import ArtinMatthews.GiantTwoSidedRootIntervalBudget


set_option backward.privateInPublic true
@[expose] public section

/-! Relative scalar replacement for the literal source loss, source moment
length, used-prime modulus and root interval. -/

namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section

def giantSourceResidueRelativeError (x : ℝ) (S : Finset (GiantCandidateGroupIndex x))
    {M : ℕ} (labels : Fin (giantTwoSidedSourceMomentLength x + 1) →
      MarkedPhysicalMarking (fun i : S => giantCandidateGroup x i.val) M)
    (q : ℝ) (offset : Fin (giantTwoSidedSourceMomentLength x + 1) → ℤ)
    (X : ℝ) (a : ℕ) : ℝ :=
  let P := giantSourceInactivePrimes x S labels
  let f := giantSourceResidueLoss x q offset
  let Q := giantTwoSidedActiveModulus labels
  let H := ((⌈2 * X⌉₊ - ⌈X⌉₊ : ℕ) : ℝ) / Q
  let V := ∏ p ∈ P, (1 - scalarWeightedResidueMean f p)
  |scalarWeightedResidueCountIco P f ⌈X⌉₊ ⌈2 * X⌉₊ Q a - H * V| / (H * V)

theorem giantCandidateSourceResidue_relative (M : ℕ) (A : ℝ) (hA : 0 ≤ A)
    {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, ∀ (S : Finset (GiantCandidateGroupIndex x))
      (labels : Fin (giantTwoSidedSourceMomentLength x + 1) →
        MarkedPhysicalMarking (fun i : S => giantCandidateGroup x i.val) M)
      (q : ℝ), 0 ≤ q → q ≤ 1 →
      ∀ (offset : Fin (giantTwoSidedSourceMomentLength x + 1) → ℤ)
        (X : ℝ), x ^ γ ≤ X → ∀ a : ℕ,
        giantSourceResidueRelativeError x S labels q offset X a ≤
          2 * (Real.log x) ^ (-A * (giantTwoSidedSourceMomentLength x : ℝ)) +
            Real.exp (-γ * Real.log x / 4) := by
  filter_upwards [giantSourceResidueMean_cap, giantSourceResidueMean_sum,
    giantSourceResidueEndpoint_cost A hA, giantSourceResidueCost_budget A hA M hγ,
    giantCandidateActiveModulus_bound M, giantCandidateRootInterval_budget hγ,
    eventually_gt_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_gt_atTop (1 : ℝ)]
    with x hcap hsum hcost hbudget hmodulus hinterval hx hL
  intro S labels q hq0 hq1 offset X hX a
  let P := giantSourceInactivePrimes x S labels
  let f := giantSourceResidueLoss x q offset
  let Q := giantTwoSidedActiveModulus labels
  let n := giantTwoSidedSourceMomentLength x
  have hprime : ∀ p ∈ P, p.Prime := fun p hp =>
    (giantCandidateFullPrimes_range hx hL.le (giantSourceInactivePrimes_subset x S labels hp)).1
  have hgroup : ∀ (i : S) p, p ∈ giantCandidateGroup x i.val → p.Prime := by
    intro i p hp
    exact (giantCandidateFullPrimes_range hx hL.le (mem_giantCandidateFullPrimes.mpr ⟨i.val, hp⟩)).1
  have hQ : 0 < Q := giantTwoSidedActiveModulus_pos hgroup labels
  have hcop : ∀ p ∈ P, p.Coprime Q := by
    intro p hp
    exact giantTwoSidedActiveModulus_coprime hgroup labels (hprime p hp) (mem_sdiff.mp hp).2
  have horder := giantSourceResidueOrder_succ hA hL
  have hdepth := giantSourceResidueDepth_lower hA hL
  have hR : 0 ≤ giantCandidateGroupLogRate := by unfold giantCandidateGroupLogRate; positivity
  have hΛ : 0 ≤ giantSourceResidueMeanBudget x := by
    unfold giantSourceResidueMeanBudget
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hR) (Real.log_pos hL).le
  have hcap' : ∀ p ∈ P, scalarWeightedResidueMean f p ≤ 2 / 3 :=
    fun p hp => hcap q hq0 hq1 offset p (giantSourceInactivePrimes_subset x S labels hp)
  have hcost' : scalarWeightedResidueEndpointMass P f
      (giantSourceResidueOrder A x + 1) ≤
        Real.exp (giantSourceResidueCostRate A * (Real.log x) ^ (49 / 50 : ℝ)) := by
    rw [horder]
    exact hcost S M labels q hq0 hq1 offset
  have hs := scalarWeightedResidue_relative_rank_budget_Ico P f hprime
    (fun p _ r _ => (giantSourceResidueLoss_bounds hq0 hq1 offset p r).1)
    (fun p _ r _ => (giantSourceResidueLoss_bounds hq0 hq1 offset p r).2)
    (giantSourceResidueOrder A x) ⌈X⌉₊ ⌈2 * X⌉₊ Q a (hinterval X hX).1 hQ hcop
    (giantSourceResidueMeanBudget x) (Real.log x) (γ / 2)
    ((5 * M * giantCandidateGroupLogRate) * (Real.log x) ^ (49 / 50 : ℝ))
    (giantSourceResidueCostRate A * (Real.log x) ^ (49 / 50 : ℝ))
    A (n : ℝ) hΛ (zero_lt_one.trans hL) hcap' (hsum S M labels q hq0 hq1 offset)
    (by simpa only [horder] using hdepth.1) (hinterval X hX).2
    (hmodulus S labels) hcost' hbudget
    (by simpa only [horder, n] using hdepth.2)
  have hexp : -(γ / 2) * Real.log x / 2 = -γ * Real.log x / 4 := by ring
  simpa only [giantSourceResidueRelativeError, P, f, Q, n, hexp] using hs

end
end ArtinMatthews
