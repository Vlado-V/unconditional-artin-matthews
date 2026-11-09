module

public import ArtinMatthews.ShiftedVoronoiAdditiveGrowth
public import ArtinMatthews.ShiftedVoronoiRightHalfPlane
public import ArtinMatthews.ShiftedVoronoiContour


set_option backward.privateInPublic true
@[expose] public section

/-!
# The actual additive cusp-form contour shift

Absolute coefficient convergence bounds the right edge. On the left edge the
proved cusp functional equation and the actual radial Fourier Mellin identity
supply an integrable majorant. The interior growth follows from cuspidality
and the elementary reciprocal Gamma estimate. No boundary estimate or
summation formula is assumed.
-/

noncomputable section
open Complex UpperHalfPlane MeasureTheory Set Filter
open OAI.CubicReflectionKernel
open scoped MatrixGroups Topology

namespace ArtinMatthews

private theorem norm_LSeries_le_of_re_eq (a : ℕ → ℂ) (σ : ℝ)
    (ha : LSeriesSummable a (σ : ℂ)) (s : ℂ) (hs : s.re = σ) :
    ‖LSeries a s‖ ≤ ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖ := by
  have has : LSeriesSummable a s := ha.of_re_le_re (by simpa using hs.ge)
  calc
    _ ≤ ∑' n : ℕ, ‖LSeries.term a s n‖ := norm_tsum_le_tsum_norm has.norm
    _ = _ := tsum_congr fun n => by simp only [LSeries.norm_term_eq, hs, Complex.ofReal_re]

private theorem compact_mellin_vertical_integrable
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (σ : ℝ) :
    Integrable (fun t : ℝ => mellin W ((σ : ℂ) + t * Complex.I)) := by
  obtain ⟨C, _, hb⟩ := compact_source_mellin_strip_decay W a b ha hW (W.smooth ⊤) σ σ 2
  have hc : Continuous (fun t : ℝ => mellin W ((σ : ℂ) + t * Complex.I)) :=
    (compact_source_mellin_differentiable W a b ha hW (W.smooth ⊤)).continuous.comp
      (by fun_prop)
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    simpa only [div_eq_mul_inv] using
      weighted_two_to_cauchy (norm_nonneg _) t (hb σ ⟨le_rfl, le_rfl⟩ t)

/-- The right boundary of the weighted actual additive L-function is
absolutely integrable, by its convergent coefficient series. -/
theorem cuspAdditiveL_mellin_right_integrable
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods) (x : ℚ)
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) :
    Integrable (fun t : ℝ => mellin W ((2 : ℂ) + t * Complex.I) *
      cuspAdditiveL f (x : ℝ) ((2 : ℂ) + t * Complex.I)) := by
  let K : ℝ := ∑' n : ℕ, ‖LSeries.term (cuspAdditiveCoeff f (x : ℝ)) (2 : ℂ) n‖
  have hc : Continuous (fun t : ℝ => mellin W ((2 : ℂ) + t * Complex.I) *
      cuspAdditiveL f (x : ℝ) ((2 : ℂ) + t * Complex.I)) :=
    ((compact_source_mellin_differentiable W a b ha hW (W.smooth ⊤)).continuous.mul
      (cuspAdditiveL_differentiable f x).continuous).comp (by fun_prop)
  apply ((compact_mellin_vertical_integrable W a b ha hW 2).norm.mul_const K).mono'
    hc.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    rw [norm_mul, cuspAdditiveL_eq_LSeries f hperiod _ _ (by simp)]
    apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact norm_LSeries_le_of_re_eq (cuspAdditiveCoeff f (x : ℝ)) 2
      (weightOne_additiveCoeff_LSeriesSummable f hperiod _ _ (by norm_num))
      ((2 : ℂ) + t * Complex.I) (by simp)

/-- On the left half-plane, the Gamma factors in the genuine cusp functional
equation combine with the compact source to give the actual transformed Mellin datum. -/
theorem cuspAdditiveL_mellin_reflected
    {Γ : Subgroup SL(2, ℤ)} [(Γ : Subgroup (GL (Fin 2) ℝ)).IsArithmetic]
    (f : CuspForm Γ 1)
    (hperiod : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (hq : γ 1 0 ≠ 0)
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (s : ℂ) (hs : s.re < 0) :
    mellin W s * cuspAdditiveL f ((γ 0 0 : ℝ) / γ 1 0) s =
      (((2 * Real.pi : ℝ) : ℂ) ^ s * (Complex.I / (γ 1 0 : ℂ)) *
        (((γ 1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (1 - s) *
        ((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - s))) *
      LSeries (cuspAdditiveCoeff f (-(γ 1 1 : ℝ) / γ 1 0)) (1 - s) *
      mellin (normalizedRadialFourier W) (1 - s) := by
  rw [cuspAdditiveL_reflected_series f hperiod γ hγ hq s hs,
    normalizedRadialFourier_mellin_right W a b ha hW (1 - s)
      (by simp only [Complex.sub_re, Complex.one_re]; linarith), sub_sub_cancel]
  simp only [div_eq_mul_inv]
  ring

/-- Absolute integrability on the line `re s = -1`, derived by combining
modularity with the actual transformed Mellin datum on `re s = 2`. -/
theorem cuspAdditiveL_mellin_left_integrable
    {Γ : Subgroup SL(2, ℤ)} [(Γ : Subgroup (GL (Fin 2) ℝ)).IsArithmetic]
    (f : CuspForm Γ 1)
    (hperiod : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (hq : γ 1 0 ≠ 0)
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) :
    Integrable (fun t : ℝ => mellin W ((-1 : ℂ) + t * Complex.I) *
      cuspAdditiveL f ((γ 0 0 : ℝ) / γ 1 0) ((-1 : ℂ) + t * Complex.I)) := by
  have hLd : Differentiable ℂ (cuspAdditiveL f ((γ 0 0 : ℝ) / γ 1 0)) := by
    simpa only [Rat.cast_div, Rat.cast_intCast] using
      cuspAdditiveL_differentiable f ((γ 0 0 : ℚ) / γ 1 0)
  have hc : Continuous (fun t : ℝ => mellin W ((-1 : ℂ) + t * Complex.I) *
      cuspAdditiveL f ((γ 0 0 : ℝ) / γ 1 0) ((-1 : ℂ) + t * Complex.I)) :=
    ((compact_source_mellin_differentiable W a b ha hW (W.smooth ⊤)).continuous.mul
      hLd.continuous).comp (by fun_prop)
  have hiN : Integrable (fun t : ℝ => mellin (normalizedRadialFourier W)
      (1 - ((-1 : ℂ) + t * Complex.I))) := by
    convert (normalizedRadialFourier_mellin_vertical_integrable_right W a b ha hW
      2 (by norm_num)).comp_neg using 1
    funext t
    congr 1
    push_cast
    ring
  let K : ℝ := ∑' n : ℕ,
    ‖LSeries.term (cuspAdditiveCoeff f (-(γ 1 1 : ℝ) / γ 1 0)) (2 : ℂ) n‖
  let P : ℝ := (2 * Real.pi) ^ (-1 : ℝ) * ‖Complex.I / (γ 1 0 : ℂ)‖ *
    ((γ 1 0 : ℝ) ^ 2) ^ (2 : ℝ) * (2 * Real.pi) ^ (-2 : ℝ)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hp : 0 < 2 * Real.pi := by positivity
  have hQ : 0 < (γ 1 0 : ℝ) ^ 2 := sq_pos_of_ne_zero (by exact_mod_cast hq)
  have hPn (t : ℝ) :
      ‖((2 * Real.pi : ℝ) : ℂ) ^ ((-1 : ℂ) + t * Complex.I) *
        (Complex.I / (γ 1 0 : ℂ)) *
        (((γ 1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (1 - ((-1 : ℂ) + t * Complex.I)) *
        ((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - ((-1 : ℂ) + t * Complex.I)))‖ = P := by
    dsimp [P]
    simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.add_re, Complex.neg_re,
      Complex.one_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero, Complex.sub_re]
    norm_num
  apply (hiN.norm.const_mul (P * K)).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    rw [cuspAdditiveL_mellin_reflected f hperiod γ hγ hq W a b ha hW _ (by simp),
      norm_mul, norm_mul, hPn]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply mul_le_mul_of_nonneg_left _ hP
    exact norm_LSeries_le_of_re_eq _ 2
      (weightOne_additiveCoeff_LSeriesSummable f hperiod _ _ (by norm_num))
      (1 - ((-1 : ℂ) + t * Complex.I)) (by norm_num)

/-- The genuine contour shift used in weight-one Voronoi summation, with
both edge integrability and interior growth discharged for an actual cusp form. -/
theorem cuspAdditiveL_mellin_contour
    {Γ : Subgroup SL(2, ℤ)} [(Γ : Subgroup (GL (Fin 2) ℝ)).IsArithmetic]
    (f : CuspForm Γ 1)
    (hperiod : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (hq : γ 1 0 ≠ 0)
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) :
    (∫ t : ℝ, mellin W ((-1 : ℂ) + t * Complex.I) *
      cuspAdditiveL f ((γ 0 0 : ℝ) / γ 1 0) ((-1 : ℂ) + t * Complex.I)) =
    ∫ t : ℝ, mellin W ((2 : ℂ) + t * Complex.I) *
      cuspAdditiveL f ((γ 0 0 : ℝ) / γ 1 0) ((2 : ℂ) + t * Complex.I) := by
  let x : ℚ := (γ 0 0 : ℚ) / γ 1 0
  have hLd : Differentiable ℂ (cuspAdditiveL f ((γ 0 0 : ℝ) / γ 1 0)) := by
    simpa only [x, Rat.cast_div, Rat.cast_intCast] using cuspAdditiveL_differentiable f x
  have hWd := compact_source_mellin_differentiable W a b ha hW (W.smooth ⊤)
  obtain ⟨B, hB, hbound⟩ := cuspAdditiveL_strip_exponential_bound f x (-1) 2
  obtain ⟨C, hC, hCbound⟩ := compact_source_mellin_strip_decay W a b ha hW (W.smooth ⊤)
    (-1) 2 0
  have hr : Integrable (fun t : ℝ => mellin W ((2 : ℂ) + t * Complex.I) *
      cuspAdditiveL f ((γ 0 0 : ℝ) / γ 1 0) ((2 : ℂ) + t * Complex.I)) := by
    simpa only [x, Rat.cast_div, Rat.cast_intCast] using
      cuspAdditiveL_mellin_right_integrable f hperiod x W a b ha hW
  have he := integral_eq_of_exponential_strip_growth
    (fun s => mellin W s * cuspAdditiveL f ((γ 0 0 : ℝ) / γ 1 0) s)
    (-1) 2 Real.pi (C * B) (by norm_num) Real.pi_pos.le (mul_nonneg hC.le hB)
    (fun s _ _ => (hWd s).mul (hLd s))
    (by simpa using cuspAdditiveL_mellin_left_integrable f hperiod γ hγ hq W a b ha hW)
    (by simpa using hr) (by
    intro σ hσ t
    have hw : ‖mellin W ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
      simpa using hCbound σ hσ t
    have hl : ‖cuspAdditiveL f ((γ 0 0 : ℝ) / γ 1 0) ((σ : ℂ) + t * Complex.I)‖ ≤
        B * Real.exp (Real.pi * |t|) := by
      simpa only [x, Rat.cast_div, Rat.cast_intCast, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul,
        sub_zero, add_zero, Complex.add_im, Complex.mul_im, Complex.I_im, mul_one,
        zero_add] using hbound ((σ : ℂ) + t * Complex.I) (by simpa using hσ)
    rw [norm_mul]
    exact (mul_le_mul hw hl (norm_nonneg _) hC.le).trans_eq (by ring))
  simpa using he

end ArtinMatthews
