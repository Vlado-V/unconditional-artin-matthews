module

public import ArtinMatthews.VaryingKummerAnalyticMixedUnitAverageSymmetry


set_option backward.privateInPublic true
@[expose] public section

/-! Exact signature-dependent affine unit-log shift and radial scale of the
trace-dual Gaussian. The factor two at every complex place is retained. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def mixedDualMeanLog : ℝ :=
  (∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ)*Real.log (InfinitePlace.mult w)) /
    (Module.finrank ℚ K : ℝ)

def mixedDualRadialScale : ℝ := Real.exp (mixedDualMeanLog K)

def mixedDualLogShift : logSpace K := fun w =>
  (InfinitePlace.mult w.1 : ℝ) * (Real.log (InfinitePlace.mult w.1) - mixedDualMeanLog K)

theorem mixedDualRadialScale_pos : 0 < mixedDualRadialScale K := Real.exp_pos _

theorem mixedDualPlaceLog_sum :
    (∑ w : InfinitePlace K,
      (InfinitePlace.mult w : ℝ)*(Real.log (InfinitePlace.mult w)-mixedDualMeanLog K)) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Nat.cast_sum, InfinitePlace.sum_mult_eq]
  unfold mixedDualMeanLog
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  field_simp
  ring

theorem mixedRestoredPlaceLog_dualShift (w : InfinitePlace K) :
    mixedRestoredPlaceLog K (mixedDualLogShift K) w =
      (InfinitePlace.mult w : ℝ)*(Real.log (InfinitePlace.mult w)-mixedDualMeanLog K) := by
  by_cases hw : w = w₀
  · subst w
    have H := mixedDualPlaceLog_sum K
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at H
    simp only [mixedRestoredPlaceLog, dite_true, mixedDualLogShift]
    linarith
  · simp [mixedRestoredPlaceLog, hw, mixedDualLogShift]

theorem mixedPlaceWeight_dualShift (w : InfinitePlace K) :
    mixedPlaceWeight K (mixedDualLogShift K) w =
      (InfinitePlace.mult w : ℝ) / mixedDualRadialScale K := by
  rw [mixedPlaceWeight, mixedRestoredPlaceLog_dualShift,
    mul_div_cancel_left₀ _ InfinitePlace.mult_coe_ne_zero, Real.exp_sub,
    Real.exp_log (Nat.cast_pos.mpr (InfinitePlace.mult_pos (w := w)))]
  rfl

theorem mixedDualMeanLog_signature :
    mixedDualMeanLog K =
      (2*(InfinitePlace.nrComplexPlaces K : ℝ)*Real.log 2)/(Module.finrank ℚ K : ℝ) := by
  unfold mixedDualMeanLog
  rw [InfinitePlace.sum_eq_sum_add_sum]
  simp only [InfinitePlace.mult_isReal, InfinitePlace.mult_isComplex, Nat.cast_one,
    Nat.cast_ofNat, Real.log_one, mul_zero, Finset.sum_const_zero, zero_add,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem mixedPlaceWeight_neg (u : logSpace K) (w : InfinitePlace K) :
    mixedPlaceWeight K (-u) w = (mixedPlaceWeight K u w)⁻¹ := by
  have he : mixedRestoredPlaceLog K (-u) w = -mixedRestoredPlaceLog K u w := by
    unfold mixedRestoredPlaceLog
    split_ifs <;> simp
  simp only [mixedPlaceWeight, he, neg_div, Real.exp_neg]

/-- Exact pointwise Gaussian multiplier identity used after Poisson duality. -/
theorem mixedDualGaussian_weight (u : logSpace K) (w : InfinitePlace K) :
    (InfinitePlace.mult w : ℝ)*mixedPlaceWeight K (-u) w =
      mixedDualRadialScale K * mixedPlaceWeight K (mixedDualLogShift K-u) w := by
  rw [sub_eq_add_neg, mixedPlaceWeight_add, mixedPlaceWeight_dualShift]
  have h := (mixedDualRadialScale_pos K).ne'
  field_simp

end
end ArtinMatthews.VaryingKummerAnalytic
