module

public import Mathlib.MeasureTheory.Integral.Prod


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted Cauchy--Schwarz and Fubini for actual Mellin isolation integrals.
The hypotheses assert convergence of the input products, not an L² conclusion. -/
namespace ArtinMatthews
open MeasureTheory Set
open scoped ENNReal
noncomputable section

private theorem weighted_integral_sq_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (w b : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hwi : Integrable w μ)
    (hbi : Integrable (fun x => w x*b x) μ)
    (hb₂ : Integrable (fun x => w x*(b x)^2) μ) :
    (∫ x, w x*b x ∂μ)^2 ≤ (∫ x, w x ∂μ)*(∫ x, w x*(b x)^2 ∂μ) := by
  let W := ∫ x, w x ∂μ
  let B := ∫ x, w x*b x ∂μ
  let Q := ∫ x, w x*(b x)^2 ∂μ
  have hW : 0 ≤ W := integral_nonneg hw
  by_cases hzero : W = 0
  · have he : w =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hw hwi).mp hzero
    have hB : B = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [he] with x hx
      simp [hx]
    change B^2 ≤ W*Q
    simp [hzero,hB]
  · let r := B/W
    have he (x : α) : w x*(b x-r)^2 =
        w x*(b x)^2-(2*r)*(w x*b x)+r^2*w x := by ring
    have hpos : 0 ≤ ∫ x, w x*(b x-r)^2 ∂μ :=
      integral_nonneg (fun x => mul_nonneg (hw x) (sq_nonneg _))
    simp_rw [he] at hpos
    have hsub : Integrable (fun x => w x*(b x)^2-(2*r)*(w x*b x)) μ :=
      hb₂.sub (hbi.const_mul (2*r))
    rw [integral_add hsub (hwi.const_mul (r^2)),
      integral_sub hb₂ (hbi.const_mul (2*r)),integral_const_mul,integral_const_mul] at hpos
    change 0 ≤ Q-2*r*B+r^2*W at hpos
    have heval : W*(Q-2*r*B+r^2*W) = W*Q-B^2 := by
      dsimp [r]
      field_simp
      ring
    have hp := mul_nonneg hW hpos
    rw [heval] at hp
    change B^2 ≤ W*Q
    linarith

theorem markedMellinIsolation_weighted_L2
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (F : α → ℂ) (A : α → β → ℂ) (hF : Integrable F μ)
    (hfirst : Integrable (fun p : α × β => F p.1*A p.1 p.2) (μ.prod ν))
    (hsecond : Integrable (fun p : α × β => ‖F p.1‖*‖A p.1 p.2‖^2) (μ.prod ν))
    {E : ℝ} (henergy : ∀ᵐ ξ ∂μ, (∫ t, ‖A ξ t‖^2 ∂ν) ≤ E) :
    Integrable (fun t => ‖∫ ξ, F ξ*A ξ t ∂μ‖^2) ν ∧
      (∫ t, ‖∫ ξ, F ξ*A ξ t ∂μ‖^2 ∂ν) ≤ (∫ ξ, ‖F ξ‖ ∂μ)^2*E := by
  let W := ∫ ξ, ‖F ξ‖ ∂μ
  have hW : 0 ≤ W := integral_nonneg (fun _ => norm_nonneg _)
  have hpoint : ∀ᵐ t ∂ν, ‖∫ ξ, F ξ*A ξ t ∂μ‖^2 ≤
      W*(∫ ξ, ‖F ξ‖*‖A ξ t‖^2 ∂μ) := by
    filter_upwards [hfirst.prod_left_ae,hsecond.prod_left_ae] with t h₁ h₂
    have hb : Integrable (fun ξ => ‖F ξ‖*‖A ξ t‖) μ := by
      simpa only [norm_mul] using h₁.norm
    have hcs := weighted_integral_sq_le μ (fun ξ => ‖F ξ‖) (fun ξ => ‖A ξ t‖)
      (fun _ => norm_nonneg _) hF.norm hb h₂
    have hn := norm_integral_le_integral_norm (fun ξ => F ξ*A ξ t) (μ := μ)
    simp only [norm_mul] at hn
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs
  have hmajor : Integrable (fun t => W*(∫ ξ, ‖F ξ‖*‖A ξ t‖^2 ∂μ)) ν :=
    hsecond.integral_prod_right.const_mul W
  have hout : Integrable (fun t => ‖∫ ξ, F ξ*A ξ t ∂μ‖^2) ν := by
    apply hmajor.mono' (hfirst.integral_prod_right.aestronglyMeasurable.norm.pow 2)
    filter_upwards [hpoint] with t ht
    change ‖‖∫ ξ, F ξ*A ξ t ∂μ‖^2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact ht
  refine ⟨hout,?_⟩
  have hint := integral_mono_ae hout hmajor hpoint
  rw [integral_const_mul,← integral_integral_swap hsecond] at hint
  have hinner : (fun ξ => ∫ t, ‖F ξ‖*‖A ξ t‖^2 ∂ν) =
      (fun ξ => ‖F ξ‖*(∫ t, ‖A ξ t‖^2 ∂ν)) := by
    ext ξ
    exact integral_const_mul _ _
  rw [hinner] at hint
  have hI : Integrable (fun ξ => ‖F ξ‖*(∫ t, ‖A ξ t‖^2 ∂ν)) μ := by
    rw [← hinner]
    exact hsecond.integral_prod_left
  have hupper := integral_mono_ae hI (hF.norm.mul_const E)
    (henergy.mono (fun ξ hξ => mul_le_mul_of_nonneg_left hξ (norm_nonneg _)))
  rw [integral_mul_const] at hupper
  have hh := mul_le_mul_of_nonneg_left hupper hW
  change _ ≤ W^2*E
  nlinarith


theorem markedMellinIsolation_weighted_L2_of_bounded
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [IsFiniteMeasure ν]
    (F : α → ℂ) (A : α → β → ℂ) (hF : Integrable F μ)
    (hA : AEStronglyMeasurable (fun p : α × β => A p.1 p.2) (μ.prod ν))
    {B : ℝ} (hbound : ∀ᵐ p : α × β ∂μ.prod ν, ‖A p.1 p.2‖ ≤ B)
    {E : ℝ} (henergy : ∀ᵐ ξ ∂μ, (∫ t, ‖A ξ t‖^2 ∂ν) ≤ E) :
    Integrable (fun t => ‖∫ ξ, F ξ*A ξ t ∂μ‖^2) ν ∧
      (∫ t, ‖∫ ξ, F ξ*A ξ t ∂μ‖^2 ∂ν) ≤ (∫ ξ, ‖F ξ‖ ∂μ)^2*E := by
  have hfirst : Integrable (fun p : α × β => F p.1*A p.1 p.2) (μ.prod ν) :=
    (hF.comp_fst ν).mul_bdd hA hbound
  have hsecond : Integrable (fun p : α × β => ‖F p.1‖*‖A p.1 p.2‖^2) (μ.prod ν) := by
    apply (hF.norm.comp_fst ν).mul_bdd (c := B^2) (hA.norm.pow 2)
    filter_upwards [hbound] with p hp
    change ‖‖A p.1 p.2‖^2‖ ≤ B^2
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hp 2
  exact markedMellinIsolation_weighted_L2 μ ν F A hF hfirst hsecond henergy

theorem markedMellinIsolation_weighted_L2_interval
    (F : ℝ → ℂ) (A : ℝ → ℝ → ℂ) (hF : Integrable F)
    (hA : Continuous (fun p : ℝ × ℝ => A p.1 p.2)) {B : ℝ}
    (hbound : ∀ ξ t : ℝ, ‖A ξ t‖ ≤ B) (T : ℝ) {E : ℝ}
    (henergy : ∀ ξ : ℝ, (∫ t in Icc (-T) T, ‖A ξ t‖^2) ≤ E) :
    IntegrableOn (fun t => ‖∫ ξ : ℝ, F ξ*A ξ t‖^2) (Icc (-T) T) ∧
      (∫ t in Icc (-T) T, ‖∫ ξ : ℝ, F ξ*A ξ t‖^2) ≤
        (∫ ξ : ℝ, ‖F ξ‖)^2*E := by
  let : IsFiniteMeasure (volume.restrict (Icc (-T) T)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
  exact markedMellinIsolation_weighted_L2_of_bounded volume
    (volume.restrict (Icc (-T) T)) F A hF hA.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => hbound p.1 p.2))
    (Filter.Eventually.of_forall henergy)

end
end ArtinMatthews
