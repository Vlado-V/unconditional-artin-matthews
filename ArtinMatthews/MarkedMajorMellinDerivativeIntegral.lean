module

public import ArtinMatthews.MarkedMajorMellinDerivative
public import Mathlib.MeasureTheory.Integral.Bochner.Set


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory
open scoped ContDiff
noncomputable section

theorem markedMajorMellinKernel_derivative_eq_zero (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {a b R X : ℝ} (ha : 0 < a) (hX : 0 < X)
    (hρ : tsupport ρ ⊆ Icc a b) (hρ' : tsupport ρ' ⊆ Icc a b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (theta : ℝ) (n : ℕ) (p : ℝ × ℝ)
    (hp : p ∉ markedMajorMellinSupportBox a b R) :
    iteratedFDeriv ℝ n (markedMajorMellinKernelFun ρ ρ' ψ X theta) p = 0 := by
  by_contra hn
  exact hp (markedMajorMellinKernel_tsupport ρ ρ' ψ ha hX hρ hρ' hψ theta
    (support_iteratedFDeriv_subset n hn))

theorem markedMajorMellinKernel_derivative_integrable (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {a b R X : ℝ} (ha : 0 < a) (hX : 0 < X)
    (hρ : tsupport ρ ⊆ Icc a b) (hρ' : tsupport ρ' ⊆ Icc a b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (theta : ℝ) (n : ℕ) :
    Integrable (iteratedFDeriv ℝ n (markedMajorMellinKernelFun ρ ρ' ψ X theta)) :=
  ((markedMajorMellinKernel_contDiff ρ ρ' ψ X theta).continuous_iteratedFDeriv (by simp)).integrable_of_hasCompactSupport
    ((markedMajorMellinKernel_hasCompactSupport ρ ρ' ψ ha hX hρ hρ' hψ theta).iteratedFDeriv n)

/-- Actual L1 derivative bounds, with constants independent of the moving scale. -/
theorem markedMajorMellinKernel_derivative_L1_bound (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {a b R : ℝ} (ha : 0 < a)
    (hρ : tsupport ρ ⊆ Icc a b) (hρ' : tsupport ρ' ⊆ Icc a b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X ≥ 1, ∀ theta : ℝ,
      (∫ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n (markedMajorMellinKernelFun ρ ρ' ψ X theta) p‖) ≤
        C*(1+|theta|)^n := by
  obtain ⟨C,hC,hbound⟩ := markedMajorMellinKernel_compact_derivative_bound ρ ρ' ψ a b R n
  let K := markedMajorMellinSupportBox a b R
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  refine ⟨C*(volume.real K+1),by positivity,fun X hX theta => ?_⟩
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have heq : (∫ p in K, ‖iteratedFDeriv ℝ n (markedMajorMellinKernelFun ρ ρ' ψ X theta) p‖) =
      ∫ p, ‖iteratedFDeriv ℝ n (markedMajorMellinKernelFun ρ ρ' ψ X theta) p‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
      rw [markedMajorMellinKernel_derivative_eq_zero ρ ρ' ψ ha hXpos hρ hρ' hψ theta n p hp,norm_zero])
  have H := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := K)
    (f := fun p : ℝ × ℝ => ‖iteratedFDeriv ℝ n (markedMajorMellinKernelFun ρ ρ' ψ X theta) p‖)
    hK.measure_lt_top (fun p hp => by
      simpa only [norm_norm] using hbound X hX theta p hp)
  rw [heq,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at H
  calc
    _ ≤ (C*(1+|theta|)^n)*volume.real K := H
    _ ≤ (C*(volume.real K+1))*(1+|theta|)^n := by nlinarith [pow_nonneg (by positivity : 0 ≤ 1+|theta|) n]

end
end ArtinMatthews
