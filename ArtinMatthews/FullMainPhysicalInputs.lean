module

public import ArtinMatthews.GiantOrdinaryFinalReduction
public import ArtinMatthews.GiantCandidateRetainedCorrelationAssembly
public import ArtinMatthews.SourceReflectionActualSieve


set_option backward.privateInPublic true
@[expose] public section

/-! Transport the physical comparison and reflected expansion estimates to
the fixed-cutoff receiver for the original simultaneous primitive root theorem. -/

namespace ArtinMatthews

open Set
open scoped ContDiff
noncomputable section

theorem giantMainOrdinaryTupleCancellationInput_of_comparison
    (hcomparison : ∀ T : ℝ, 1 < T → T < 2 →
      Function.support giantMainSmoothCutoff ⊆ Ioo 1 T →
      ∀ (M : ℕ) [NeZero M], ∀ m ≥ 20000,
        let γ := markedSieveExponent (giantMainEpsilon / 4) m
        ∀ j ∈ Finset.Icc 2 ⌈2 / γ⌉₊, ∀ χ : DirichletCharacter ℂ M,
          ∀ (K : ℕ) (e : Fin K → ℝ),
            (∀ i, (1/10 : ℝ) < e i ∧ e i < 1/5) → Function.Injective e →
            GiantCandidatePerformedComparisonLogSaving e χ giantMainEpsilon γ (1/2) j
              (fun t => ((t * giantMainSmoothCutoff t : ℝ) : ℂ))) :
    GiantOrdinaryTupleCancellationInput giantMainEpsilon giantMainSmoothCutoff := by
  apply giantMainOrdinaryTupleCancellationInput_of_retained_correlation
  intro T hT₁ hT₂ hs M instM m hm γ j hj threshold hthreshold χ
  refine ⟨0, fun K _ e he hinj => ?_⟩
  have hγ : 0 < γ :=
    markedSieveExponent_pos (div_pos giantMainEpsilon_bounds.1 (by norm_num)) m
  have he' (i : Fin K) : 0 < e i ∧ e i ≤ 1/5 :=
    ⟨(by norm_num : (0 : ℝ) < 1/10).trans (he i).1, (he i).2.le⟩
  exact giantCandidateRetainedCorrelationLogSaving_of_comparison e he' χ
    giantMainEpsilon_bounds.1 (giantMainEpsilon_bounds.2.trans (by norm_num))
    giantMainSmoothCutoff giantMainSmoothCutoff_spec.1 zero_lt_one
    (zero_lt_one.trans hT₁) (hs.trans Ioo_subset_Icc_self) hγ (by norm_num) (by norm_num)
    hthreshold j (zero_lt_two.trans_le (Finset.mem_Icc.mp hj).1)
    (hcomparison T hT₁ hT₂ hs M m hm j hj χ K e he hinj)

open NumberField IsDedekindDomain AllowedGenerators SourceEulerAssembly VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped NumberField

variable (q : ℕ) [NeZero q]
local notation "Kq" => twelfthCyclotomicField q
local notation "hz" => twelfthAngularRoot_isPrimitiveRoot q

theorem twelfthAngularSourceBounds_of_literal_expansions
    (hprincipal : ∃ (U : Type) (_ : Fintype U)
      (A : ExteriorUnitSixthClasses (sourceHilbertSet Kq (angularReflectedSeed Kq ⊤)) →
        SourceReflectionExpansionData Kq (angularReflectedSeed Kq ⊤) U),
      SourceReflectionLiteralExpansion Kq (angularReflectedSeed Kq ⊤) hz
        (principalAngularTrivialRay Kq) (angularReflectedSeed_bad_subset Kq ⊤) A)
    (hprimitive : ∀ (J : Ideal (𝓞 Kq)) (_ : J ≠ ⊥) (ψ : EvenIdealRayCharacter Kq J),
      IsPrimitiveOnIdeals ψ.residue → ψ.IsNonprincipal →
      ψ.coefficient ≠ ψ.inverse.coefficient →
      Real.log (J.absNorm : ℝ) ≤ (12 * q : ℝ) * ((72 * (q : ℝ) ^ 2 + 2) * Real.log (12 * q)) →
      ∃ (U : Type) (_ : Fintype U)
        (A : ExteriorUnitSixthClasses (sourceHilbertSet Kq (angularReflectedSeed Kq J)) →
          SourceReflectionExpansionData Kq (angularReflectedSeed Kq J) U),
        SourceReflectionLiteralExpansion Kq (angularReflectedSeed Kq J) hz ψ
          (angularReflectedSeed_bad_subset Kq J) A) :
    TwelfthAngularSourceBounds q := by
  refine twelfthAngularSourceBounds_of_reflected q ?_ ?_
  · obtain ⟨U, hU, A, hA⟩ := hprincipal
    let _ := hU
    exact sourcePoissonReflectedSecondMoment_of_expansion_actual Kq (angularReflectedSeed Kq ⊤)
      hz (principalAngularTrivialRay Kq) (angularReflectedSeed_bad_subset Kq ⊤) A hA
  · intro J hJ ψ hprim hnp hreal hcond
    obtain ⟨U, hU, A, hA⟩ := hprimitive J hJ ψ hprim hnp hreal hcond
    let _ := hU
    exact sourcePoissonReflectedSecondMoment_of_expansion_actual Kq (angularReflectedSeed Kq J)
      hz ψ (angularReflectedSeed_bad_subset Kq J) A hA

end
end ArtinMatthews
