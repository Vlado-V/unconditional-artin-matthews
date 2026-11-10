module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine integer-translate unfolding of an absolutely integrable real-line function. -/
noncomputable section
open Set MeasureTheory
namespace ArtinMatthews

def spectralIntegerTranslationEquiv : ℤ ≃ AddSubgroup.zmultiples (1:ℝ) :=
  Equiv.ofBijective (fun k => ⟨(k:ℝ),by
    exact ⟨k,by simp⟩⟩) ⟨by
      intro k l h
      have he : (k:ℝ)=(l:ℝ) := congrArg (fun a : AddSubgroup.zmultiples (1:ℝ) => (a:ℝ)) h
      exact_mod_cast he,by
      intro a
      obtain ⟨k,hk⟩ := a.property
      refine ⟨k,Subtype.ext ?_⟩
      simpa using hk⟩

theorem spectralIntegerTranslationEquiv_apply (k : ℤ) :
    (spectralIntegerTranslationEquiv k : ℝ)=(k:ℝ) := rfl

theorem spectralIntegerPeriodUnfolding (f : ℝ → ℂ) (hf : Integrable f) :
    (∑' k : ℤ, ∫ x in (0:ℝ)..1, f ((k:ℝ)+x)) = ∫ x : ℝ, f x := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).integral_eq_tsum'' f hf
  rw [← spectralIntegerTranslationEquiv.tsum_eq] at h
  simpa only [zero_add,AddSubgroup.vadd_def,vadd_eq_add,spectralIntegerTranslationEquiv_apply,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] using h.symm

theorem spectralIntegerPeriodUnfolding_shift (f : ℝ → ℂ) (hf : Integrable f) (a : ℝ) :
    (∑' k : ℤ, ∫ x in (0:ℝ)..1, f (x+(k:ℝ)+a)) = ∫ x : ℝ, f x := by
  have h := spectralIntegerPeriodUnfolding (fun x => f (x+a)) (hf.comp_add_right a)
  rw [integral_add_right_eq_self] at h
  simpa only [add_comm] using h

end ArtinMatthews
