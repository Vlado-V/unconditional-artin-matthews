module

public import ArtinMatthews.MarkedMajorMellinIsolationBase
public import Mathlib.MeasureTheory.Integral.Bochner.Set


set_option backward.privateInPublic true
@[expose] public section

/-! Quantitative derivative integrals for the actual logarithmic cutoff.
All constants precede the modulation parameter. -/
namespace ArtinMatthews
open MeasureTheory Set
open scoped ContDiff FourierTransform SchwartzMap
noncomputable section

private theorem integral_norm_derivative_le_compact_interval
    (f : ℝ → ℂ) (n : ℕ) {u v M : ℝ}
    (hs : tsupport f ⊆ Icc u v)
    (hb : ∀ x ∈ Icc u v, ‖iteratedFDeriv ℝ n f x‖ ≤ M) :
    (∫ x : ℝ, ‖iteratedFDeriv ℝ n f x‖) ≤ M*volume.real (Icc u v) := by
  have hz (x : ℝ) (hx : x ∉ Icc u v) : ‖iteratedFDeriv ℝ n f x‖ = 0 := by
    have hzero : iteratedFDeriv ℝ n f x = 0 := by
      apply Classical.byContradiction
      intro h
      exact hx (hs (support_iteratedFDeriv_subset n h))
    rw [hzero,norm_zero]
  have he := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hz
  have h := norm_setIntegral_le_of_norm_le_const_ae'
    (μ := volume) (s := Icc u v) (f := fun x => ‖iteratedFDeriv ℝ n f x‖)
    (isCompact_Icc.measure_lt_top) (Filter.Eventually.of_forall (fun x hx => by simpa using hb x hx))
  rw [he,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun x => norm_nonneg _))] at h
  exact h

theorem markedMellinIsolation_derivative_integral_bound
    (η : ℝ → ℂ) (hη : ContDiff ℝ ∞ η) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support η ⊆ Icc a b) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ,
      (∫ z : ℝ, ‖iteratedFDeriv ℝ n (markedMellinIsolationSchwartz η hη ha hsupp θ) z‖) ≤
        C*(1+|θ|)^n := by
  obtain ⟨C,hC,hb⟩ := markedOscillatoryFamily_compact_derivative_bound
    (fun z => η (Real.exp z)) (fun z => -(2*Real.pi)*Real.exp z)
    (hη.comp Real.contDiff_exp) (by fun_prop) (Icc (Real.log a) (Real.log b)) isCompact_Icc n
  let V := volume.real (Icc (Real.log a) (Real.log b))
  have hV : 0 ≤ V := measureReal_nonneg
  refine ⟨C*(V+1),by positivity,?_⟩
  intro θ
  have h := integral_norm_derivative_le_compact_interval
    (markedMellinIsolationLogProfile η θ) n
    (markedMellinIsolationLogProfile_tsupport η ha hsupp θ) (hb θ)
  change (∫ z : ℝ, ‖iteratedFDeriv ℝ n (markedMellinIsolationLogProfile η θ) z‖) ≤ _
  change _ ≤ C*(1+|θ|)^n*V at h
  nlinarith [mul_nonneg hC.le (pow_nonneg (by positivity : 0 ≤ 1+|θ|) n)]

theorem markedMellinIsolation_first_three_integrals_bound
    (η : ℝ → ℂ) (hη : ContDiff ℝ ∞ η) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support η ⊆ Icc a b) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ,
      ((∫ z : ℝ, ‖iteratedFDeriv ℝ 0 (markedMellinIsolationSchwartz η hη ha hsupp θ) z‖) +
       (∫ z : ℝ, ‖iteratedFDeriv ℝ 1 (markedMellinIsolationSchwartz η hη ha hsupp θ) z‖) +
       (∫ z : ℝ, ‖iteratedFDeriv ℝ 2 (markedMellinIsolationSchwartz η hη ha hsupp θ) z‖)) ≤
        C*(1+|θ|)^2 := by
  obtain ⟨C₀,hC₀,h₀⟩ := markedMellinIsolation_derivative_integral_bound η hη ha hsupp 0
  obtain ⟨C₁,hC₁,h₁⟩ := markedMellinIsolation_derivative_integral_bound η hη ha hsupp 1
  obtain ⟨C₂,hC₂,h₂⟩ := markedMellinIsolation_derivative_integral_bound η hη ha hsupp 2
  refine ⟨C₀+C₁+C₂,by positivity,?_⟩
  intro θ
  have hbase : 1 ≤ 1+|θ| := by linarith [abs_nonneg θ]
  have hh₀ := h₀ θ
  have hh₁ := h₁ θ
  have hh₂ := h₂ θ
  simp only [pow_zero,pow_one,mul_one] at hh₀ hh₁
  have hp₀ : 1 ≤ (1+|θ|)^2 := one_le_pow₀ hbase
  have hp₁ : 1+|θ| ≤ (1+|θ|)^2 := le_self_pow₀ hbase (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hp₀ hC₀.le,mul_le_mul_of_nonneg_left hp₁ hC₁.le]

end
end ArtinMatthews
