module

public import ArtinMatthews.GiantSignedSourceAbsoluteCost
public import ArtinMatthews.GiantSmallConditioningActual


set_option backward.privateInPublic true
@[expose] public section

/-! The source small-conditioning cost is fixed before the ideal
construction and copied-slot choice. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantSignedSourceSmallConditioning_exists
    {q vmin C₀ : ℝ} (ell : ℕ) (hq : 0 < q) (hq1 : q < 1)
    (hvmin : 0 < vmin) (hC₀ : 0 ≤ C₀) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧
      ∀ (S : Type*) [Fintype S] [DecidableEq S] (PS : S → Finset ℕ)
        [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val],
        (∀ j p, p ∈ PS j → p.Prime) → Pairwise (fun i j => Disjoint (PS i) (PS j)) →
        (∀ j, vmin ≤ bandReciprocalMass (PS j)) →
      ∀ (k : ℕ) (L : ℝ), 0 < L → (Fintype.card S : ℝ) ≤ C₀ * Real.log L →
      ∀ f : GiantTwoSidedResidueState PS (k+ell) → ℂ,
        (∑ d : MarkedPhysicalMarking PS k,
          giantSmallResidueEnergy (giantSmallConditioningMap PS k ell q d f)) ≤
            L ^ Cs * giantSmallStateEnergy f := by
  obtain ⟨BS, hBS, hbudget⟩ := giantSignedSmallRowBudget_exists hq hq1 hvmin ell
  let R := max 1 BS
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  refine ⟨C₀ * Real.log R, mul_nonneg hC₀ (Real.log_nonneg hR1), ?_⟩
  intro S _ _ PS _ hPS hdis hVmin k L hL hgroups f
  have hV (j : S) : 0 < bandReciprocalMass (PS j) := hvmin.trans_le (hVmin j)
  have hsmall := giantSmallConditioning_norm_sum hPS hdis hV hq hq1.le hBS
    (fun j z => hbudget _ (hVmin j) z) f
  have hcost : BS ^ Fintype.card S ≤ L ^ (C₀ * Real.log R) := calc
    _ ≤ R ^ Fintype.card S := pow_le_pow_left₀ hBS (le_max_right _ _) _
    _ = Real.exp (Real.log R * (Fintype.card S : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hR]
    _ ≤ Real.exp (Real.log L * (C₀ * Real.log R)) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ Real.log R * (C₀ * Real.log L) := mul_le_mul_of_nonneg_left hgroups (Real.log_nonneg hR1)
        _ = _ := by ring
    _ = _ := (Real.rpow_def_of_pos hL _).symm
  have hf0 : 0 ≤ giantSmallStateEnergy f := by
    unfold giantSmallStateEnergy giantTwoSidedResidueHaarStateMass markedPhysicalMass
    exact mul_nonneg
      (div_nonneg (Finset.prod_nonneg fun j _ => pow_nonneg (inv_nonneg.mpr (hV j).le) _)
        (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  exact hsmall.trans (mul_le_mul_of_nonneg_right hcost hf0)

end
end ArtinMatthews
