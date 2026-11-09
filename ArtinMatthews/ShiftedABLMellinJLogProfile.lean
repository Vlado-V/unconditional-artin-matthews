module

public import ArtinMatthews.ShiftedABLMellinModuli
public import ArtinMatthews.SpectralJLogSeminorm


set_option backward.privateInPublic true
@[expose] public section

/-! The literal Mellin modulus weight is a fixed compact logarithmic
amplitude with the original two unrestricted Mellin heights. -/
namespace ArtinMatthews
open Set Complex OAI
open scoped ContDiff
noncomputable section

def shiftedABLMellinJLogAmplitude (v : ℝ) : ℂ :=
  (circleSmoothCutoff (3*Real.exp (-v)) : ℂ)*(Real.exp v : ℂ)

def shiftedABLMellinJLogPhase (v : ℝ) : ℝ := 4*Real.pi*v

theorem shiftedABLMellinJLogAmplitude_smooth :
    ContDiff ℝ ∞ shiftedABLMellinJLogAmplitude := by
  unfold shiftedABLMellinJLogAmplitude
  apply ContDiff.mul
  · exact Complex.ofRealCLM.contDiff.comp
      (circleSmoothCutoff_contDiff.comp (contDiff_const.mul (Real.contDiff_exp.comp contDiff_id.neg)))
  · exact Complex.ofRealCLM.contDiff.comp Real.contDiff_exp

theorem shiftedABLMellinJLogPhase_smooth :
    ContDiff ℝ ∞ shiftedABLMellinJLogPhase :=
  contDiff_const.mul contDiff_id

theorem shiftedABLMellinJLogAmplitude_tsupport :
    tsupport shiftedABLMellinJLogAmplitude ⊆ Icc (-Real.log 2) 0 := by
  apply closure_minimal _ isClosed_Icc
  intro v hv
  have hcut : circleSmoothCutoff (3*Real.exp (-v)) ≠ 0 := by
    intro hz
    exact hv (by simp only [shiftedABLMellinJLogAmplitude, hz, Complex.ofReal_zero, zero_mul])
  have hs : 3*Real.exp (-v) ∈ Ioo (3 : ℝ) 6 := by
    rw [← circleSmoothCutoff_support]
    exact hcut
  have hlo : 1 < Real.exp (-v) := by linarith [hs.1]
  have hhi : Real.exp (-v) < 2 := by linarith [hs.2]
  have hv0 : 0 < -v := by
    apply Real.exp_lt_exp.mp
    simpa only [Real.exp_zero] using hlo
  have hv1 : -v < Real.log 2 := by
    apply Real.exp_lt_exp.mp
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hhi
  exact ⟨by linarith, by linarith⟩

theorem shiftedABLMellinModulusWeight_log
    {F L : ℕ} (hF : 0 < F) (hL : 0 < L) (z : ℝ × ℝ) (v : ℝ) :
    shiftedABLMellinModulusWeight F L z
      ((3*(L : ℝ)/(F : ℝ))*Real.exp (-v)) =
      markedOscillatoryFamily shiftedABLMellinJLogAmplitude shiftedABLMellinJLogPhase
        (z.1+z.2) v := by
  have hF0 : (F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hF.ne'
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have h₁ : (F : ℝ)*((3*(L : ℝ)/(F : ℝ))*Real.exp (-v))/(L : ℝ) =
      3*Real.exp (-v) := by field_simp [hF0,hL0] <;> ring
  have h₂ : 3*(L : ℝ)/((F : ℝ)*((3*(L : ℝ)/(F : ℝ))*Real.exp (-v))) =
      Real.exp v := by
    rw [Real.exp_neg]
    field_simp [hF0,hL0,(Real.exp_pos v).ne'] <;> ring
  have h₃ : (F : ℝ)*((3*(L : ℝ)/(F : ℝ))*Real.exp (-v))/(3*(L : ℝ)) =
      Real.exp (-v) := by field_simp [hF0,hL0] <;> ring
  unfold shiftedABLMellinModulusWeight circleSmoothScaled shiftedABLMellinCirclePhase
  rw [h₁,h₂,h₃,Real.log_exp]
  unfold FourierBridge.logPhase markedOscillatoryFamily shiftedABLMellinJLogAmplitude
    markedOscillatoryPhase shiftedABLMellinJLogPhase markedRealOscillator
  rw [mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring

def shiftedABLMellinJNumerator (n : ℕ) (ρ : ℤ) : ℝ :=
  4*Real.pi*Real.sqrt ((ρ.natAbs : ℝ)*(n : ℝ))

def shiftedABLMellinJScale (L n r : ℕ) (ρ : ℤ) : ℝ :=
  shiftedABLMellinJNumerator n ρ/(Real.sqrt (r : ℝ)*(3*(L : ℝ)))

def shiftedABLMellinJRadial (F L n r : ℕ) (ρ : ℤ) (z : ℝ × ℝ) (x : ℝ) : ℂ :=
  shiftedABLMellinModulusWeight F L z
    (shiftedABLMellinJNumerator n ρ/((F : ℝ)*Real.sqrt (r : ℝ)*x))

theorem shiftedABLMellinJNumerator_pos {n : ℕ} {ρ : ℤ}
    (hn : 0 < n) (hρ : ρ ≠ 0) : 0 < shiftedABLMellinJNumerator n ρ := by
  unfold shiftedABLMellinJNumerator
  have hρn : 0 < ρ.natAbs := Int.natAbs_pos.mpr hρ
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ' : (0 : ℝ) < ρ.natAbs := by exact_mod_cast hρn
  positivity

theorem shiftedABLMellinJScale_pos {L n r : ℕ} {ρ : ℤ}
    (hL : 0 < L) (hn : 0 < n) (hr : 0 < r) (hρ : ρ ≠ 0) :
    0 < shiftedABLMellinJScale L n r ρ := by
  unfold shiftedABLMellinJScale
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  exact div_pos (shiftedABLMellinJNumerator_pos hn hρ) (by positivity)

theorem shiftedABLMellinJRadial_eq_logProfile
    {F L n r : ℕ} {ρ : ℤ} (hF : 0 < F) (hL : 0 < L)
    (hn : 0 < n) (hr : 0 < r) (hρ : ρ ≠ 0) (z : ℝ × ℝ) :
    shiftedABLMellinJRadial F L n r ρ z =
      spectralJOscillatoryLogProfile shiftedABLMellinJLogAmplitude shiftedABLMellinJLogPhase
        (shiftedABLMellinJScale L n r ρ) (z.1+z.2) := by
  have hF' : (0 : ℝ) < F := by exact_mod_cast hF
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hsqr : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hr'
  have ha := shiftedABLMellinJScale_pos hL hn hr hρ
  have hnum := shiftedABLMellinJNumerator_pos hn hρ
  funext x
  by_cases hx : 0 < x
  · have he : shiftedABLMellinJNumerator n ρ/((F : ℝ)*Real.sqrt (r : ℝ)*x) =
        (3*(L : ℝ)/(F : ℝ))*
          Real.exp (-Real.log (x/shiftedABLMellinJScale L n r ρ)) := by
      rw [Real.exp_neg, Real.exp_log (div_pos hx ha), inv_div]
      unfold shiftedABLMellinJScale
      field_simp [hF'.ne',hL'.ne',hsqr.ne',hx.ne'] <;> ring
    rw [shiftedABLMellinJRadial,he,shiftedABLMellinModulusWeight_log hF hL]
    exact (ite_eq_left hx).symm
  · have hc : shiftedABLMellinJNumerator n ρ/((F : ℝ)*Real.sqrt (r : ℝ)*x) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos hnum.le
        (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hF'.le hsqr.le) (le_of_not_gt hx))
    have hz : shiftedABLMellinJRadial F L n r ρ z x = 0 := by
      by_contra hne
      have hm := shiftedABLMellinModulusWeight_support hF hL z hne
      have hscale : 0 < 3*(L : ℝ)/(F : ℝ) := by positivity
      linarith [hm.1]
    simp only [hz, spectralJOscillatoryLogProfile, spectralJLogProfile, if_neg hx]

end
end ArtinMatthews
