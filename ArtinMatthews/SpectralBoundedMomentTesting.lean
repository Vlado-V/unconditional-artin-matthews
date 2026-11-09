module

public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.MeasureTheory.Integral.Bochner.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Vanishing bounded moments imply vanishing against every continuous
function of the bounded variable, by actual polynomial approximation. -/
noncomputable section
open Set Filter MeasureTheory
namespace ArtinMatthews

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem spectralUnitWeight_continuous_integrable {f : X → ℂ} {w : X → ℝ}
    (hf : Integrable f μ) (hw : AEMeasurable w μ) (hb : ∀ᵐ x ∂μ,w x∈Icc (0:ℝ) 1)
    (F : ℝ → ℝ) (hF : Continuous F) : Integrable (fun x => F (w x) • f x) μ := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF.continuousOn
  apply hf.bdd_smul C (hF.measurable.comp_aemeasurable hw).aestronglyMeasurable
  exact hb.mono (fun x hx => hC _ hx)

theorem spectralUnitWeight_polynomial_moment_zero {f : X → ℂ} {w : X → ℝ}
    (hf : Integrable f μ) (hw : AEMeasurable w μ) (hb : ∀ᵐ x ∂μ,w x∈Icc (0:ℝ) 1)
    (hm : ∀ n : ℕ,(∫ x,(w x)^n • f x ∂μ)=0) (P : Polynomial ℝ) :
    (∫ x,P.eval (w x) • f x ∂μ)=0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp_rw [Polynomial.eval_add,add_smul]
    rw [integral_add (spectralUnitWeight_continuous_integrable hf hw hb _ P.continuous)
      (spectralUnitWeight_continuous_integrable hf hw hb _ Q.continuous),hP,hQ,add_zero]
  | monomial n c =>
    simp_rw [Polynomial.eval_monomial,mul_smul]
    rw [integral_smul,hm,smul_zero]

theorem spectralUnitWeight_continuous_moment_zero {f : X → ℂ} {w : X → ℝ}
    (hf : Integrable f μ) (hw : AEMeasurable w μ) (hb : ∀ᵐ x ∂μ,w x∈Icc (0:ℝ) 1)
    (hm : ∀ n : ℕ,(∫ x,(w x)^n • f x ∂μ)=0) (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ x,F (w x) • f x ∂μ)=0 := by
  let J : ℂ := ∫ x,F (w x) • f x ∂μ
  let C : ℝ := ∫ x,‖f x‖ ∂μ
  have hC : 0≤C := integral_nonneg (fun _ => norm_nonneg _)
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  by_contra hzero
  have hJ : 0<‖J‖ := lt_of_not_ge hzero
  let ε := ‖J‖/(2*(C+1))
  have hden : 0<2*(C+1) := by positivity
  have hε : 0<ε := div_pos hJ hden
  obtain ⟨P,hP⟩ := exists_polynomial_near_of_continuousOn 0 1 F hF.continuousOn ε hε
  have hIntF := spectralUnitWeight_continuous_integrable hf hw hb F hF
  have hIntP := spectralUnitWeight_continuous_integrable hf hw hb (fun t => P.eval t) P.continuous
  have he : J=∫ x,(F (w x)-P.eval (w x)) • f x ∂μ := by
    simp_rw [sub_smul]
    rw [integral_sub hIntF hIntP,spectralUnitWeight_polynomial_moment_zero hf hw hb hm P,sub_zero]
  have hbound : ‖J‖≤ε*C := by
    rw [he]
    calc
      _ ≤ ∫ x,ε*‖f x‖ ∂μ := norm_integral_le_of_norm_le (hf.norm.const_mul ε) (by
        filter_upwards [hb] with x hx
        rw [norm_smul,Real.norm_eq_abs,abs_sub_comm]
        exact mul_le_mul_of_nonneg_right (hP _ hx).le (norm_nonneg _))
      _ = ε*C := integral_const_mul _ _
  have hcancel : ε*(2*(C+1))=‖J‖ := div_mul_cancel₀ _ hden.ne'
  have hlt : ε*C<ε*(2*(C+1)) := mul_lt_mul_of_pos_left (by linarith) hε
  linarith

end ArtinMatthews
