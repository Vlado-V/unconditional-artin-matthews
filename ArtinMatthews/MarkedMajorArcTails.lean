module

public import ArtinMatthews.MarkedMajorArcMangoldt
public import ArtinMatthews.MarkedMajorArcBounds
public import ArtinMatthews.MarkedMajorArcContour
public import ArtinMatthews.MarkedMajorArcRightBound
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Actual unbounded right tails of the shifted character Mangoldt Perron
integral. The bound is uniform in every character and every frequency. -/
namespace ArtinMatthews

open Complex Set MeasureTheory Erdos970

lemma marked_major_mangoldt_integrable {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x σ : ℝ} (hx : 0 < x)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (t : ℝ) :
    Integrable (fun u : ℝ => markedMajorMangoldtIntegrand χ x t
      ((σ:ℂ)+(u:ℂ)*Complex.I)) := by
  obtain ⟨C,hC,hr⟩ := marked_major_logderiv_right_bound
  have hB : 0 ≤ C+1/σ := by positivity
  have hc : Continuous (fun u : ℝ => markedMajorMangoldtIntegrand χ x t
      ((σ:ℂ)+(u:ℂ)*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    let s : ℂ := (σ:ℂ)+(u:ℂ)*Complex.I
    have hzre : 1 < (s+(1-(t:ℂ)*Complex.I)).re := by simp [s]; linarith
    have hz1 : s+(1-(t:ℂ)*Complex.I) ≠ 1 := by
      intro he
      rw [he] at hzre
      norm_num at hzre
    have hn : DirichletCharacter.LFunction χ (s+(1-(t:ℂ)*Complex.I)) ≠ 0 := by
      rw [DirichletCharacter.LFunction_eq_LSeries χ hzre]
      exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hzre
    have hline : ContinuousAt (fun u : ℝ => (σ:ℂ)+(u:ℂ)*Complex.I) u := by fun_prop
    have hg := (marked_character_logderiv_differentiableAt χ hz1 hn).continuousAt.comp
      (f:=fun u : ℝ => (σ:ℂ)+(u:ℂ)*Complex.I) hline
    have hk := (marked_perron_kernel_differentiableAt hx (s:=s)
      (by intro he; have hh:=congrArg Complex.re he; norm_num [s] at hh; linarith)
      (by intro he; have hh:=congrArg Complex.re he; norm_num [s] at hh; linarith)).continuousAt.comp
      (f:=fun u : ℝ => (σ:ℂ)+(u:ℂ)*Complex.I) hline
    exact hg.mul hk
  have hm : Integrable (fun u : ℝ => ((C+1/σ)*x^σ/σ^2)/(1+u^2)) := by
    convert integrable_inv_one_add_sq.const_mul ((C+1/σ)*x^σ/σ^2) using 1
    funext u
    exact div_eq_mul_inv _ _
  apply hm.mono' hc.aestronglyMeasurable
  filter_upwards [] with u
  have hh := hr q χ (((σ:ℂ)+(u:ℂ)*Complex.I)+(1-(t:ℂ)*Complex.I))
    (by simp; linarith) (by simp; linarith)
  simp only [Complex.add_re,Complex.sub_re,Complex.one_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,zero_mul,sub_zero,add_zero,add_sub_cancel_right] at hh
  rw [markedMajorMangoldtIntegrand,norm_mul,neg_div,norm_neg]
  exact (mul_le_mul hh (marked_perron_kernel_vertical hx hσ hσ1 u)
    (norm_nonneg _) hB).trans_eq (by simp only [div_eq_mul_inv,mul_inv_rev]; ring)

/-- The actual Perron tails decay like the inverse contour height, with no
restriction on the original frequency `t`. -/
theorem marked_major_mangoldt_right_tails :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (x σ t H : ℝ), 0 < x → 0 < σ → σ ≤ 1 → 0 < H →
      ‖VerticalIntegral (markedMajorMangoldtIntegrand χ x t) σ -
        VIntegral (markedMajorMangoldtIntegrand χ x t) σ (-H) H‖ ≤
      2*(C+1/σ)*x^σ/H := by
  obtain ⟨C,hC,hr⟩ := marked_major_logderiv_right_bound
  refine ⟨C,hC,?_⟩
  intro q _ χ x σ t H hx hσ hσ1 hH
  have hB : 0 ≤ C+1/σ := by positivity
  have hh := marked_vertical_power_tails (f:=markedMajorMangoldtIntegrand χ x t)
    (b:=σ) (D:=(C+1/σ)*x^σ) hH (by norm_num : (1:ℝ)<2)
    (marked_major_mangoldt_integrable χ hx hσ hσ1 t) ?_
  · norm_num only [show (1:ℝ)-2 = -1 by norm_num, show (2:ℝ)-1 = 1 by norm_num,
      Real.rpow_neg_one, div_one] at hh
    exact hh.trans_eq (by ring)
  intro u hu
  have hu0 : u ≠ 0 := by intro he; simp [he] at hu; linarith
  have hf := hr q χ (((σ:ℂ)+(u:ℂ)*Complex.I)+(1-(t:ℂ)*Complex.I))
    (by simp; linarith) (by simp; linarith)
  simp only [Complex.add_re,Complex.sub_re,Complex.one_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,zero_mul,sub_zero,add_zero,add_sub_cancel_right] at hf
  rw [markedMajorMangoldtIntegrand,norm_mul,neg_div,norm_neg]
  apply (mul_le_mul hf (marked_perron_kernel_horizontal hx σ hu0)
    (norm_nonneg _) hB).trans_eq
  rw [Real.rpow_neg (abs_nonneg u),Real.rpow_two,sq_abs]
  ring

end ArtinMatthews
