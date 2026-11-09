module

public import Mathlib.NumberTheory.ModularForms.Bounds
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-!
# Horizontal Fourier inversion for additive cusp-form sums

The finite kernel cancels the exponential decay of the Fourier coefficients on
any horizontal line. Its logarithmic L¹ bound is a separate analytic step.
-/

noncomputable section
open scoped BigOperators
open Complex UpperHalfPlane MeasureTheory

namespace ArtinMatthews

/-- The finite kernel compensating for the height of the horizontal line. -/
def weightedFourierKernel (N : ℕ) (y t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, (Real.exp (2 * Real.pi * n * y) : ℂ) *
    fourier (n : ℤ) (t : AddCircle (1 : ℝ))

lemma continuous_weightedFourierKernel (N : ℕ) (y : ℝ) :
    Continuous (weightedFourierKernel N y) := by
  unfold weightedFourierKernel
  fun_prop

lemma fourier_sub_real (n : ℤ) (θ x : ℝ) :
    fourier n ((θ - x : ℝ) : AddCircle (1 : ℝ)) =
      fourier n (θ : AddCircle (1 : ℝ)) * fourier (-n) (x : AddCircle (1 : ℝ)) := by
  simp only [fourier_coe_apply, Complex.ofReal_sub, Complex.ofReal_one, div_one,
    Int.cast_neg]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Finite Fourier convolution, including the compensating exponential weight. -/
theorem sum_fourierCoeffOn_eq_integral_weightedFourierKernel
    (F : ℝ → ℂ) (hF : Continuous F) (N : ℕ) (y θ : ℝ) :
    (∑ n ∈ Finset.range N, (Real.exp (2 * Real.pi * n * y) : ℂ) *
      fourierCoeffOn (by norm_num : (0 : ℝ) < 1) F (n : ℤ) *
        fourier (n : ℤ) (θ : AddCircle (1 : ℝ))) =
      ∫ x in (0 : ℝ)..1, F x * weightedFourierKernel N y (θ - x) := by
  simp_rw [weightedFourierKernel, Finset.mul_sum, fourier_sub_real]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n _
    rw [fourierCoeffOn_eq_integral]
    simp only [sub_zero, one_div_one, one_smul, smul_eq_mul]
    have heq : (fun x : ℝ => F x * ((Real.exp (2 * Real.pi * n * y) : ℂ) *
        (fourier (n : ℤ) (θ : AddCircle (1 : ℝ)) * fourier (-(n : ℤ)) (x : AddCircle (1 : ℝ))))) =
        fun x : ℝ => (Real.exp (2 * Real.pi * n * y) : ℂ) *
          (fourier (-(n : ℤ)) (x : AddCircle (1 : ℝ)) * F x) *
            fourier (n : ℤ) (θ : AddCircle (1 : ℝ)) := by
      funext x
      ring
    rw [heq, intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
    simp only [fourier_coe_apply, sub_zero]
  · intro n _
    apply Continuous.intervalIntegrable
    fun_prop

/-- A uniform bound on the horizontal function costs only the kernel's L¹ norm. -/
theorem norm_sum_fourierCoeffOn_le_kernel_integral
    (F : ℝ → ℂ) (hF : Continuous F) (N : ℕ) (y θ B : ℝ)
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖F x‖ ≤ B) :
    ‖∑ n ∈ Finset.range N, (Real.exp (2 * Real.pi * n * y) : ℂ) *
      fourierCoeffOn (by norm_num : (0 : ℝ) < 1) F (n : ℤ) *
        fourier (n : ℤ) (θ : AddCircle (1 : ℝ))‖ ≤
      B * ∫ x in (0 : ℝ)..1, ‖weightedFourierKernel N y (θ - x)‖ := by
  rw [sum_fourierCoeffOn_eq_integral_weightedFourierKernel F hF]
  calc
    _ ≤ ∫ x in (0 : ℝ)..1, ‖F x * weightedFourierKernel N y (θ - x)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ x in (0 : ℝ)..1, B * ‖weightedFourierKernel N y (θ - x)‖ := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · apply Continuous.intervalIntegrable
        exact (hF.mul ((continuous_weightedFourierKernel N y).comp
          (continuous_const.sub continuous_id))).norm
      · apply Continuous.intervalIntegrable
        exact continuous_const.mul (((continuous_weightedFourierKernel N y).comp
          (continuous_const.sub continuous_id)).norm)
      · intro x hx
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound x hx) (norm_nonneg _)
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- Actual cusp-form coefficients satisfy the finite horizontal convolution
identity; no independent coefficient expansion is postulated. -/
theorem cuspForm_sum_eq_horizontal_kernel
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (f : CuspForm Γ 1)
    (hperiod : (1 : ℝ) ∈ Γ.strictPeriods) (N : ℕ)
    {y : ℝ} (hy : 0 < y) (θ : ℝ) :
    (∑ n ∈ Finset.range N, (qExpansion 1 f).coeff n *
      fourier (n : ℤ) (θ : AddCircle (1 : ℝ))) =
      ∫ x in (0 : ℝ)..1,
        f ⟨x + y * UpperHalfPlane.I, by simpa using hy⟩ *
          weightedFourierKernel N y (θ - x) := by
  have hc (n : ℕ) := UpperHalfPlane.qExpansion_coeff_eq_exp_mul_fourierCoeffOn
    (by norm_num : (0 : ℝ) < 1)
    (SlashInvariantFormClass.periodic_comp_ofComplex f hperiod)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) hy n
  simp only [div_one] at hc
  simp_rw [hc]
  apply sum_fourierCoeffOn_eq_integral_weightedFourierKernel
  fun_prop

/-- The global weight-one cusp-form bound reduces every additive partial sum
to the L¹ norm of the explicit finite kernel at any positive height. -/
theorem weightOne_additive_sum_le_horizontal_kernel
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (y : ℝ), 0 < y → ∀ θ : ℝ,
      ‖∑ n ∈ Finset.range N, (qExpansion 1 f).coeff n *
        fourier (n : ℤ) (θ : AddCircle (1 : ℝ))‖ ≤
        (C / Real.sqrt y) *
          ∫ x in (0 : ℝ)..1, ‖weightedFourierKernel N y (θ - x)‖ := by
  obtain ⟨B, hB⟩ := CuspFormClass.exists_bound f
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro N y hy θ
  have hc (n : ℕ) := UpperHalfPlane.qExpansion_coeff_eq_exp_mul_fourierCoeffOn
    (by norm_num : (0 : ℝ) < 1)
    (SlashInvariantFormClass.periodic_comp_ofComplex f hperiod)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) hy n
  simp only [div_one] at hc
  simp_rw [hc]
  apply norm_sum_fourierCoeffOn_le_kernel_integral
  · fun_prop
  · intro x _
    calc
      ‖f ⟨x + y * UpperHalfPlane.I, by simpa using hy⟩‖ ≤ B / Real.sqrt y := by
        simpa [Real.sqrt_eq_rpow] using
          hB ⟨x + y * UpperHalfPlane.I, by simpa using hy⟩
      _ ≤ max B 0 / Real.sqrt y :=
        div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)

/-- At height `1/N`, the weight-one growth factor is exactly `sqrt N`. -/
theorem weightOne_additive_sum_le_kernel_integral
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N → ∀ θ : ℝ,
      ‖∑ n ∈ Finset.range N, (qExpansion 1 f).coeff n *
        fourier (n : ℤ) (θ : AddCircle (1 : ℝ))‖ ≤
        (C * Real.sqrt N) *
          ∫ x in (0 : ℝ)..1, ‖weightedFourierKernel N (1 / N) (θ - x)‖ := by
  obtain ⟨C, hC, hb⟩ := weightOne_additive_sum_le_horizontal_kernel f hperiod
  refine ⟨C, hC, fun N hN θ => ?_⟩
  have hy : (0 : ℝ) < 1 / N := by positivity
  simpa [Real.sqrt_div, Real.sqrt_one, div_div] using hb N (1 / N) hy θ

end ArtinMatthews
