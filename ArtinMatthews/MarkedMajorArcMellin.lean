module

public import ArtinMatthews.MarkedMajorArcSmoothing
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import PrimeNumberTheoremAnd.Erdos970.ResidueCalcOnRectangles


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine triangular Mellin inversion on every line `0 < σ ≤ 1`.
The elementary triangle transform proof is reused from OAI's
TwoPoint/Fourier/ModFivePerronInversion; the vertical bound is generalized
here to the vanishing right abscissa required by the long-prime contour. -/
namespace ArtinMatthews

open Complex Set MeasureTheory
open scoped Classical

noncomputable def markedMellinTriangle (x : ℝ) : ℂ :=
  ((max (1 - x) 0 : ℝ) : ℂ)

lemma markedMellinTriangle_hasMellin {s : ℂ} (hs : 0 < s.re) :
    HasMellin markedMellinTriangle s (1 / (s * (s + 1))) := by
  have h0 := hasMellin_one_Ioc hs
  have h1 := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simpa using (show 0 < s.re + 1 by linarith))
  have hd := hasMellin_sub h0.1 h1.1
  rw [h0.2, h1.2] at hd
  have he : ∀ t ∈ Ioi (0 : ℝ), markedMellinTriangle t =
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
        (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, ht1⟩
      simp [markedMellinTriangle, indicator_of_mem hm, max_eq_left (sub_nonneg.mpr ht1)]
    · have hm : t ∉ Ioc (0 : ℝ) 1 := fun h => ht1 h.2
      simp [markedMellinTriangle, indicator_of_notMem hm, max_eq_right (by linarith : 1 - t ≤ 0)]
  have hc : MellinConvergent markedMellinTriangle s := by
    exact hd.1.congr_fun (fun t ht => by rw [he t ht]) measurableSet_Ioi
  refine ⟨hc, ?_⟩
  calc
    mellin markedMellinTriangle s = mellin
        (fun t => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
          (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t) s := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [he t ht]
    _ = 1 / s - 1 / (s + 1) := hd.2
    _ = _ := by
      have hs0 : s ≠ 0 := by intro h; simp [h] at hs
      have hs1 : s + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
      field_simp
      ring

lemma markedMellinTriangle_continuous : Continuous markedMellinTriangle := by
  unfold markedMellinTriangle
  fun_prop


noncomputable def markedPerronKernel (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ)^s / (s*(s+1))

lemma marked_perron_denominator_vertical {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (t : ℝ) :
    σ^2*(1+t^2) ≤ ‖((σ:ℂ)+(t:ℂ)*Complex.I)*((σ:ℂ)+(t:ℂ)*Complex.I+1)‖ := by
  let z : ℂ := (σ:ℂ)+(t:ℂ)*Complex.I
  have hn : ‖z‖ ≤ ‖z+1‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply, z, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg z)
  rw [← sq, Complex.sq_norm] at hm
  have hz : Complex.normSq z = σ^2+t^2 := by simp [Complex.normSq_apply,z]; ring
  rw [hz] at hm
  rw [norm_mul]
  change σ^2*(1+t^2) ≤ ‖z‖*‖z+1‖
  have hs : σ^2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg t, mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg t)]

lemma marked_perron_kernel_vertical {x σ : ℝ} (hx : 0 < x)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (t : ℝ) :
    ‖markedPerronKernel x ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤ x^σ/(σ^2*(1+t^2)) := by
  rw [markedPerronKernel, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (by positivity)
    (marked_perron_denominator_vertical hσ hσ1 t)

lemma marked_perron_kernel_integrable {x σ : ℝ} (hx : 0 < x)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Integrable (fun t : ℝ => markedPerronKernel x ((σ:ℂ)+(t:ℂ)*Complex.I)) := by
  have h0 (t : ℝ) : (σ:ℂ)+(t:ℂ)*Complex.I ≠ 0 := by
    intro ht
    have he := congrArg Complex.re ht
    norm_num at he
    linarith
  have h1 (t : ℝ) : (σ:ℂ)+(t:ℂ)*Complex.I+1 ≠ 0 := by
    intro ht
    have he := congrArg Complex.re ht
    norm_num at he
    linarith
  have hc : Continuous (fun t : ℝ => markedPerronKernel x ((σ:ℂ)+(t:ℂ)*Complex.I)) := by
    unfold markedPerronKernel
    apply Continuous.div
    · exact (show Continuous (fun t : ℝ => (σ:ℂ)+(t:ℂ)*Complex.I) by
        fun_prop).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    · fun_prop
    · exact fun t => mul_ne_zero (h0 t) (h1 t)
  have hi : Integrable (fun t : ℝ => x^σ/(σ^2*(1+t^2))) := by
    convert integrable_inv_one_add_sq.const_mul (x^σ/σ^2) using 1
    ext t
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  exact hi.mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (marked_perron_kernel_vertical hx hσ hσ1))

lemma marked_mellin_triangle_vertical_integrable {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Complex.VerticalIntegrable (mellin markedMellinTriangle) σ := by
  have hi := marked_perron_kernel_integrable (by norm_num : (0:ℝ)<1) hσ hσ1
  apply hi.congr
  filter_upwards [] with t
  have hs : 0 < (((σ:ℂ)+(t:ℂ)*Complex.I)).re := by simpa using hσ
  rw [(markedMellinTriangle_hasMellin hs).2]
  simp [markedPerronKernel]

theorem marked_perron_inversion {x σ : ℝ} (hx : 0 < x) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Erdos970.VerticalIntegral' (markedPerronKernel x) σ = markedMellinTriangle (1 / x) := by
  have hsp : 0 < σ := by linarith
  have hi := mellinInv_mellin_eq σ markedMellinTriangle (one_div_pos.mpr hx)
    (markedMellinTriangle_hasMellin (by simpa using hsp)).1
    (marked_mellin_triangle_vertical_integrable hσ hσ1) (markedMellinTriangle_continuous.continuousAt)
  have hpoint : ∀ t : ℝ,
      ((1 / x : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
        mellin markedMellinTriangle ((σ : ℂ) + (t : ℂ) * Complex.I) =
          markedPerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    rw [show (1 / x : ℝ) = x⁻¹ by ring, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg hx.le, Complex.cpow_neg, inv_inv,
      (markedMellinTriangle_hasMellin (by simpa using hsp)).2]
    unfold markedPerronKernel
    ring
  have hconst : (1 / (2 * (Real.pi : ℂ) * Complex.I)) * Complex.I =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [← hi]
  simp only [Erdos970.VerticalIntegral', Erdos970.VerticalIntegral, mellinInv,
    smul_eq_mul, ← mul_assoc, hconst]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => (hpoint t).symm


end ArtinMatthews
