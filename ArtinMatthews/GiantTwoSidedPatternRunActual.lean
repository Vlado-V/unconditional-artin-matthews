module

public import ArtinMatthews.GiantTwoSidedPatternRunCharge
public import ArtinMatthews.GiantCandidateSelectedGroups
public import ArtinMatthews.MarkedBonferroniTail


set_option backward.privateInPublic true
@[expose] public section

/-! The actual candidate-prime lower bound discharges the shift-size
condition uniformly. The resulting chronological identity retains every
original reciprocal band factor. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section

theorem giantCandidatePattern_step_size_eventually (C₂ : ℝ) :
    ∀ᶠ x : ℝ in atTop,∀ step : ℤ,(step.natAbs:ℝ)≤(Real.log x)^C₂ →
      ∀ p∈giantCandidateFullPrimes x,step.natAbs<p := by
  have ht := (rpow_mul_exp_neg_rpow_tendsto C₂
    (by norm_num : (0:ℝ)<28/100) (by norm_num : (0:ℝ)<1)).comp Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ),
    ht.eventually (Iio_mem_nhds (zero_lt_one : (0:ℝ)<1))] with x hx hL hsmall
  intro step hstep p hp
  have hbound := (giantCandidateFullPrimes_range hx hL hp).2.1
  have hlog : (Real.log x)^C₂ < Real.exp ((Real.log x)^(28/100:ℝ)) := by
    apply (div_lt_one (Real.exp_pos _)).mp
    simpa only [div_eq_mul_inv,← Real.exp_neg,neg_one_mul,Function.comp_def] using hsmall
  exact_mod_cast (hstep.trans_lt hlog).trans_le hbound

theorem giantCandidatePatternPath_run_charge_eventually (C₂ : ℝ) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      ∀ (k ell n : ℕ) (C : Fin n → S → Finset (Fin k)) (Z : Finset ℕ)
        (s : Fin (n+1) → GiantTwoSidedEndpointState P (k+ell) Z)
        (π τ : Fin n → S → Equiv.Perm (Fin (k+ell)))
        (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ),
        (∀ i,0<(step i).natAbs) → (∀ i,((step i).natAbs:ℝ)≤(Real.log x)^C₂) →
        (∀ i,GiantTwoSidedPatternCondition (C i) (step i)
          (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
          (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)) →
        markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell)*
          (∏ i,giantTwoSidedPatternFreshMass P (C i) ell) =
          ∏ j,∏ p∈P j,(bandReciprocalMass (P j))⁻¹^
            (giantTwoSidedPathPrimeRuns (fun i => (s i).val.2) j p) := by
  filter_upwards [giantCandidatePattern_step_size_eventually C₂,
    giantCandidateFullPrimes_prime_upper_eventually,giantCandidateSelectedGroups_geometry_eventually]
    with x hsize hprime hgeo
  intro S
  let P (i : S) := giantCandidateGroup x i.val
  dsimp only
  intro k ell n C Z s π τ aux step hstep hstepBound h
  have hP (i : S) (p : ℕ) (hp : p∈P i) : p.Prime :=
    (hprime p (mem_giantCandidateFullPrimes.mpr ⟨i.val,hp⟩)).1
  exact giantTwoSidedPatternPath_run_charge hP (hgeo S).1 s π τ aux step hstep
    (fun i j p hp => hsize (step i) (hstepBound i) p (mem_giantCandidateFullPrimes.mpr ⟨j.val,hp⟩)) h

end
end ArtinMatthews
