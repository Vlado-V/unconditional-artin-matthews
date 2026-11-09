module

public import ArtinMatthews.VaryingKummerAnalyticMixedGaussianUnfolding
public import ArtinMatthews.VaryingKummerAnalyticMixedPartialDedekind


set_option backward.privateInPublic true
@[expose] public section

/-! Ordinary-unit balancing in the actual mixed embedding. The compact unit
logarithm fundamental domain supplies a field-dependent constant, uniformly
for every nonzero field element and every infinite place. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedRestoredPlaceLog_of_sum_zero (f : InfinitePlace K → ℝ)
    (hf : ∑ w, f w = 0) (w : InfinitePlace K) :
    mixedRestoredPlaceLog K (fun v => f v.val) w = f w := by
  by_cases hw : w = w₀
  · subst w
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hf
    simp only [mixedRestoredPlaceLog, dite_true]
    linarith
  · simp only [mixedRestoredPlaceLog,dite_eq_right hw]

theorem exists_unit_translate_mem_mixedUnitLogDomain (u : logSpace K) :
    ∃ z : (𝓞 K)ˣ, logEmbedding K (Additive.ofMul z) + u ∈ mixedUnitLogDomain K := by
  let B := (basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)
  obtain ⟨v,hv,_⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B u
  have hvL : (v : logSpace K) ∈ unitLattice K := by
    rw [← (basisUnitLattice K).ofZLatticeBasis_span ℝ]
    exact v.property
  obtain ⟨z,hz⟩ := mixedUnitLogOnto_surjective K ⟨v,hvL⟩
  refine ⟨z.toMul,?_⟩
  have he := congrArg Subtype.val hz
  change logEmbedding K z = (v : logSpace K) at he
  change (v : logSpace K) + u ∈ mixedUnitLogDomain K at hv
  change logEmbedding K z + u ∈ mixedUnitLogDomain K
  rw [he]
  exact hv

theorem exists_mixedPlaceWeight_domain_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ mixedUnitLogDomain K, ∀ w : InfinitePlace K,
      mixedPlaceWeight K u w ≤ C := by
  let F : logSpace K → InfinitePlace K → ℝ := fun u w => mixedPlaceWeight K u w
  have hF : Continuous F := continuous_pi (fun w => mixedPlaceWeight_continuous K w)
  obtain ⟨C,hC⟩ := ((mixedUnitLogDomain_bounded K).isCompact_closure.image hF).isBounded.exists_norm_le
  refine ⟨|C|+1,by positivity,fun u hu w => ?_⟩
  have hCu : ‖F u‖ ≤ C := hC _ ⟨u,subset_closure hu,rfl⟩
  have hw : mixedPlaceWeight K u w ≤ ‖F u‖ :=
    (le_abs_self _).trans (norm_le_pi_norm (F u) w)
  exact hw.trans (hCu.trans (by linarith [le_abs_self C]))

def mixedElementMeanLog (a : K) : ℝ :=
  Real.log |(Algebra.norm ℚ a : ℝ)| / Module.finrank ℚ K

def mixedElementBalancedLog (a : K) : logSpace K := fun w =>
  (InfinitePlace.mult w.val : ℝ) * (Real.log (w.val a) - mixedElementMeanLog K a)

theorem mixedElement_weighted_log_sum {a : K} (ha : a ≠ 0) :
    (∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w a)) =
      Real.log |(Algebra.norm ℚ a : ℝ)| := by
  have hpos (w : InfinitePlace K) : 0 < w a :=
    lt_of_le_of_ne (apply_nonneg w a) (Ne.symm ((map_ne_zero w).mpr ha))
  have H := Real.log_prod (s := (Finset.univ : Finset (InfinitePlace K)))
    (f := fun w => (w a)^w.mult) (fun w _ => (pow_pos (hpos w) w.mult).ne')
  simp only [Real.log_pow] at H
  rw [InfinitePlace.prod_eq_abs_norm, Rat.cast_abs] at H
  exact H.symm

theorem mixedElementBalancedLog_restored {a : K} (ha : a ≠ 0) (w : InfinitePlace K) :
    mixedRestoredPlaceLog K (mixedElementBalancedLog K a) w =
      (w.mult : ℝ) * (Real.log (w a) - mixedElementMeanLog K a) := by
  refine mixedRestoredPlaceLog_of_sum_zero K
    (fun v => (v.mult : ℝ) * (Real.log (v a) - mixedElementMeanLog K a)) ?_ w
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,← Nat.cast_sum,
    InfinitePlace.sum_mult_eq,mixedElement_weighted_log_sum K ha,mixedElementMeanLog]
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K).ne'
  field_simp
  ring

theorem mixedElementBalancedLog_weight {a : K} (ha : a ≠ 0) (w : InfinitePlace K) :
    mixedPlaceWeight K (mixedElementBalancedLog K a) w =
      w a * Real.exp (-mixedElementMeanLog K a) := by
  rw [mixedPlaceWeight,mixedElementBalancedLog_restored K ha,
    mul_div_cancel_left₀ _ InfinitePlace.mult_coe_ne_zero,
    sub_eq_add_neg,Real.exp_add,Real.exp_log]
  exact lt_of_le_of_ne (apply_nonneg w a) (Ne.symm ((map_ne_zero w).mpr ha))

theorem exists_unit_mixed_place_balanced :
    ∃ C : ℝ, 0 < C ∧ ∀ a : K, a ≠ 0 → ∃ z : (𝓞 K)ˣ,
      ∀ w : InfinitePlace K,
        w ((z : K)*a) ≤ C * |(Algebra.norm ℚ a : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := exists_mixedPlaceWeight_domain_bound K
  refine ⟨C,hC,fun a ha => ?_⟩
  obtain ⟨z,hz⟩ := exists_unit_translate_mem_mixedUnitLogDomain K (mixedElementBalancedLog K a)
  refine ⟨z,fun w => ?_⟩
  have hw := hbound _ hz w
  rw [mixedPlaceWeight_add,mixedPlaceWeight_unit,mixedElementBalancedLog_weight K ha] at hw
  have H := mul_le_mul_of_nonneg_right hw (Real.exp_pos (mixedElementMeanLog K a)).le
  have he : Real.exp (-mixedElementMeanLog K a) * Real.exp (mixedElementMeanLog K a) = 1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  have hnorm : 0 < |(Algebra.norm ℚ a : ℝ)| := abs_pos.mpr (by
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr ha : Algebra.norm ℚ a ≠ 0))
  rw [mul_assoc,mul_assoc,he,mul_one] at H
  rw [map_mul]
  convert H using 1
  rw [Real.rpow_def_of_pos hnorm,mixedElementMeanLog]
  congr 2
  ring


theorem exists_balanced_idealElementRepresentative
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ C : ℝ, 0 < C ∧ ∀ J : integralIdealClassFiber I,
      ∃ a : nonzeroIdealElements I, relativeElementClassMap I a = J ∧
        ∀ w : InfinitePlace K,
          w (a.val : K) ≤ C * (FractionalIdeal.absNorm J.val.val : ℝ) ^
            (1 / (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨C,hC,hbalance⟩ := exists_unit_mixed_place_balanced K
  refine ⟨C * (FractionalIdeal.absNorm I.val : ℝ) ^
    (1 / (Module.finrank ℚ K : ℝ)),
    mul_pos hC (Real.rpow_pos_of_pos (fractionalIdeal_absNorm_pos I) _),fun J => ?_⟩
  obtain ⟨z,hz⟩ := hbalance (idealElementRepresentative I J).val.val
    (idealElementRepresentative I J).val.ne_zero
  refine ⟨idealElementUnitAction I z (idealElementRepresentative I J),?_,fun w => ?_⟩
  · rw [relativeElementClassMap_unitAction,idealElementRepresentative_spec]
  · have H := hz w
    rw [idealElementRepresentative_absNorm,
      Real.mul_rpow (fractionalIdeal_absNorm_pos I).le (fractionalIdeal_absNorm_pos J.val).le] at H
    change w ((z : K) * (idealElementRepresentative I J).val.val) ≤ _
    simpa only [mul_assoc] using H

theorem exists_balanced_idealElementRepresentative_norm
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ C : ℝ, 0 < C ∧ ∀ J : integralIdealClassFiber I,
      ∃ a : nonzeroIdealElements I, relativeElementClassMap I a = J ∧
        ‖mixedEmbedding K (a.val : K)‖ ≤ C * (FractionalIdeal.absNorm J.val.val : ℝ) ^
          (1 / (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨C,hC,hbalance⟩ := exists_balanced_idealElementRepresentative K I
  refine ⟨C,hC,fun J => ?_⟩
  obtain ⟨a,ha,hbound⟩ := hbalance J
  refine ⟨a,ha,?_⟩
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  apply Finset.sup'_le
  intro w _
  rw [mixedEmbedding.normAtPlace_apply]
  exact hbound w

end
end ArtinMatthews.VaryingKummerAnalytic
