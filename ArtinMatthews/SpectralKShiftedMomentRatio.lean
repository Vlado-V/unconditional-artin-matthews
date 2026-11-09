module

public import ArtinMatthews.SpectralKShiftedMoment
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv


set_option backward.privateInPublic true
@[expose] public section

/-! The shifted square moment is the exact imaginary-order moment times
a positive real Gamma ratio. On a compact real-order strip this ratio is
uniformly bounded before the spectral parameter is chosen. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein

namespace ArtinMatthews

def spectralKShiftedMomentRatio (k : ℕ) (δ : ℝ) : ℝ :=
  Real.Gamma ((k : ℝ)+1/2-δ)*Real.Gamma ((k : ℝ)+1/2+δ)/(Real.Gamma ((k : ℝ)+1/2))^2

theorem spectralKShiftedMomentRatio_complex (k : ℕ) (δ : ℝ) :
    (spectralKShiftedMomentRatio k δ : ℂ) =
      Complex.Gamma ((k : ℂ)+1/2-δ)*Complex.Gamma ((k : ℂ)+1/2+δ)/
        (Complex.Gamma ((k : ℂ)+1/2))^2 := by
  unfold spectralKShiftedMomentRatio
  rw [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
    ← Complex.Gamma_ofReal,← Complex.Gamma_ofReal,← Complex.Gamma_ofReal]
  push_cast
  rfl

theorem spectralKShiftedMoment_eq_ratio (k : ℕ) (δ t : ℝ)
    (hδ : |δ| < (k : ℝ)+1/2) :
    spectralKShiftedMoment k δ t = spectralKShiftedMomentRatio k δ*spectralKSquareMoment k t := by
  have ha : 0 < ((k : ℂ)+1/2).re := by norm_num;positivity
  have hs : 0 < (2*(k : ℂ)+1).re := by norm_num;positivity
  have hGa := Complex.Gamma_ne_zero_of_re_pos ha
  have hGs := Complex.Gamma_ne_zero_of_re_pos hs
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul,spectralKShiftedMoment_closed k δ t hδ,
    spectralKShiftedMomentRatio_complex,spectralKSquareMoment_closed]
  have hGa' : Complex.Gamma ((1/2 : ℂ)+(k : ℂ)) ≠ 0 := by simpa only [add_comm] using hGa
  field_simp [hGa,hGa',hGs]
  ring_nf
  simp only [mul_assoc,mul_inv_cancel₀ hGa',mul_one]

theorem spectralKShiftedMomentRatio_nonneg (k : ℕ) (δ : ℝ)
    (hδ : |δ| < (k : ℝ)+1/2) : 0 ≤ spectralKShiftedMomentRatio k δ := by
  have hm : 0 < (k : ℝ)+1/2-δ := by linarith [le_abs_self δ]
  have hp : 0 < (k : ℝ)+1/2+δ := by linarith [neg_le_abs δ]
  unfold spectralKShiftedMomentRatio
  exact div_nonneg (mul_nonneg (Real.Gamma_pos_of_pos hm).le (Real.Gamma_pos_of_pos hp).le) (sq_nonneg _)

theorem spectralKShiftedMomentRatio_bound (k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hBk : B < (k : ℝ)+1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, |δ| ≤ B → spectralKShiftedMomentRatio k δ ≤ C := by
  have hGamma : ContinuousOn Real.Gamma (Ioi (0 : ℝ)) := by
    intro x hx
    change 0 < x at hx
    exact (Real.differentiableAt_Gamma (fun n => by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)).continuousAt.continuousWithinAt
  have hm : ContinuousOn (fun δ : ℝ => Real.Gamma ((k : ℝ)+1/2-δ)) (Icc (-B) B) :=
    hGamma.comp (continuous_const.sub continuous_id).continuousOn (fun δ hδ => by
      change 0 < (k : ℝ)+1/2-δ
      linarith [hδ.2])
  have hp : ContinuousOn (fun δ : ℝ => Real.Gamma ((k : ℝ)+1/2+δ)) (Icc (-B) B) :=
    hGamma.comp (continuous_const.add continuous_id).continuousOn (fun δ hδ => by
      change 0 < (k : ℝ)+1/2+δ
      linarith [hδ.1])
  have hc : ContinuousOn (spectralKShiftedMomentRatio k) (Icc (-B) B) :=
    (hm.mul hp).div_const _
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨by linarith, hB⟩)
  refine ⟨C+1,by linarith,?_⟩
  intro δ hδ
  have hd := hC δ (abs_le.mp hδ)
  have hv : spectralKShiftedMomentRatio k δ ≤ C := (le_abs_self _).trans
    (by simpa only [Real.norm_eq_abs] using hd)
  exact hv.trans (by linarith)

end ArtinMatthews
