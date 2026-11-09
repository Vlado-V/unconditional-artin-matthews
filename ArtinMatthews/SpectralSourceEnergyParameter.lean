module

public import ArtinMatthews.SpectralEnergyTest
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The principal and complementary spectral parameters on the full
nonnegative energy axis, and bounded continuous frequency tests. -/

noncomputable section
open Set

namespace ArtinMatthews

def spectralSourceParameter (l : ℝ) : ℂ :=
  (Real.sqrt (l-1/4) : ℂ)+(Real.sqrt (1/4-l) : ℂ)*Complex.I

theorem spectralSourceParameter_continuous : Continuous spectralSourceParameter := by
  unfold spectralSourceParameter
  fun_prop

theorem spectralSourceParameter_principal (l : ℝ) (hl : 1/4 ≤ l) :
    spectralSourceParameter l = (Real.sqrt (l-1/4) : ℂ) := by
  unfold spectralSourceParameter
  have hz : Real.sqrt (1/4-l) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
  rw [hz,Complex.ofReal_zero,zero_mul,add_zero]

theorem spectralSourceParameter_sq (l : ℝ) : spectralSourceParameter l^2 = (l : ℂ)-1/4 := by
  by_cases hl : 1/4 ≤ l
  · rw [spectralSourceParameter_principal l hl,← Complex.ofReal_pow,Real.sq_sqrt (by linarith)]
    push_cast
    rfl
  · unfold spectralSourceParameter
    rw [Real.sqrt_eq_zero_of_nonpos (by linarith),Complex.ofReal_zero,zero_add,mul_pow,
      Complex.I_sq,← Complex.ofReal_pow,Real.sq_sqrt (by linarith)]
    push_cast
    ring

theorem spectralSourceParameter_im_bound (l : ℝ) (hl : 0 ≤ l) :
    |(spectralSourceParameter l).im| ≤ 1/2 := by
  have hs : Real.sqrt (1/4-l) ≤ Real.sqrt (1/4) := Real.sqrt_le_sqrt (by linarith)
  have hq : Real.sqrt (1/4) = (1/2 : ℝ) := by norm_num
  simp only [spectralSourceParameter,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
    Complex.ofReal_re,Complex.I_im,mul_one,Complex.I_re,mul_zero,zero_add,add_zero]
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  simpa only [hq] using hs

theorem spectralSourceParameter_frequency (t : ℝ) :
    spectralSourceParameter (1/4+t^2) = ((|t| : ℝ) : ℂ) := by
  rw [spectralSourceParameter_principal _ (by nlinarith [sq_nonneg t])]
  norm_num only [add_sub_cancel_left,Real.sqrt_sq_eq_abs]

theorem spectralSourceParameter_zero : spectralSourceParameter 0 = Complex.I/2 := by
  norm_num [spectralSourceParameter]
  ring

theorem spectralSourceFrequency_comp_continuous (F : ℂ → ℂ)
    (hF : ∀ z, |z.im| ≤ 1/2 → ContinuousAt F z) :
    ContinuousOn (fun l : ℝ => F (spectralSourceParameter l)) (Ici 0) := by
  intro l hl
  exact (hF _ (spectralSourceParameter_im_bound l hl)).comp_continuousWithinAt
    spectralSourceParameter_continuous.continuousAt.continuousWithinAt

theorem spectralSourceFrequency_energy_bound (F : ℂ → ℂ)
    (hF : ∀ z, |z.im| ≤ 1/2 → ContinuousAt F z)
    (C : ℝ) (hC : ∀ t : ℝ, ‖F (t : ℂ)‖ ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ l : ℝ, 0 ≤ l → ‖F (spectralSourceParameter l)‖ ≤ B := by
  have hc := (spectralSourceFrequency_comp_continuous F hF).mono
    (show Icc (0 : ℝ) (1/4) ⊆ Ici 0 from fun _ h => h.1)
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by norm_num))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨M+C+1,by linarith,?_⟩
  intro l hl
  by_cases hp : l ≤ 1/4
  · exact (hM l ⟨hl,hp⟩).trans (by linarith)
  · rw [spectralSourceParameter_principal l (le_of_not_ge hp)]
    exact (hC _).trans (by linarith)

def spectralSourceEnergyTest (F : ℂ → ℂ)
    (hF : ∀ z, |z.im| ≤ 1/2 → ContinuousAt F z)
    (C : ℝ) (hC : ∀ t : ℝ, ‖F (t : ℂ)‖ ≤ C) : SpectralEnergyTest :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun l => F (spectralSourceParameter l))
    ((spectralSourceFrequency_comp_continuous F hF).domRestrict)
    (Classical.choose (spectralSourceFrequency_energy_bound F hF C hC))
    (fun l => (Classical.choose_spec (spectralSourceFrequency_energy_bound F hF C hC)).2 l l.property)

theorem spectralSourceEnergyTest_apply (F : ℂ → ℂ)
    (hF : ∀ z, |z.im| ≤ 1/2 → ContinuousAt F z)
    (C : ℝ) (hC : ∀ t : ℝ, ‖F (t : ℂ)‖ ≤ C) (l : Ici (0 : ℝ)) :
    spectralSourceEnergyTest F hF C hC l = F (spectralSourceParameter l) := rfl

theorem spectralSourceEnergyTest_continuous_symbol (F : ℂ → ℂ)
    (hF : ∀ z, |z.im| ≤ 1/2 → ContinuousAt F z)
    (C : ℝ) (hC : ∀ t : ℝ, ‖F (t : ℂ)‖ ≤ C)
    (heven : ∀ z, F (-z) = F z) (t : ℝ) :
    spectralContinuousTestSymbol (spectralSourceEnergyTest F hF C hC) t = F (t : ℂ) := by
  change F (spectralSourceParameter (1/4+t^2)) = F (t : ℂ)
  rw [spectralSourceParameter_frequency]
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht),Complex.ofReal_neg,heven]

end ArtinMatthews
