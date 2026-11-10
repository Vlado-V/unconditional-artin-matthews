module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Covering.Besicovitch


set_option backward.privateInPublic true
@[expose] public section

/-! The Bessel Sturm operator and its compact positive test core. -/
namespace ArtinMatthews.SourceSturm
open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section

def sturmFlux (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) * deriv f x

def sturmD (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x : ℂ)^2 * deriv (deriv f) x + (x : ℂ) * deriv f x + (x : ℂ)^2 * f x

def sturmPair (f J : ℝ → ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), f x * J x / (x : ℂ)

def sturmL1 (f : ℝ → ℂ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), ‖f x‖ / x

theorem sturmFlux_smooth {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (sturmFlux f) :=
  Complex.ofRealCLM.contDiff.mul (contDiff_infty_iff_deriv.mp hf).2

theorem sturmD_smooth {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (sturmD f) := by
  have h : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  exact (((h.pow 2).mul (contDiff_infty_iff_deriv.mp hd).2).add (h.mul hd)).add ((h.pow 2).mul hf)

theorem sturmFlux_tsupport (f : ℝ → ℂ) :
    tsupport (sturmFlux f) ⊆ tsupport f :=
  tsupport_mul_subset_right.trans (tsupport_deriv_subset (f := f))

theorem sturmD_tsupport (f : ℝ → ℂ) :
    tsupport (sturmD f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  have hf : f x = 0 := image_eq_zero_of_notMem_tsupport hn
  have h₁ : deriv f x = 0 := deriv_of_notMem_tsupport hn
  have h₂ : deriv (deriv f) x = 0 :=
    deriv_of_notMem_tsupport (fun h => hn (tsupport_deriv_subset h))
  exact hx (by simp only [sturmD,hf,h₁,h₂,mul_zero,add_zero])

theorem sturmD_hasCompactSupport {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (sturmD f) :=
  hf.of_isClosed_subset isClosed_closure (sturmD_tsupport f)

theorem sturmD_iterate_smooth (n : ℕ) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ ((sturmD^[n]) f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact sturmD_smooth ih

theorem sturmD_iterate_tsupport (n : ℕ) (f : ℝ → ℂ) :
    tsupport ((sturmD^[n]) f) ⊆ tsupport f := by
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (sturmD_tsupport _).trans ih

theorem sturmD_iterate_hasCompactSupport (n : ℕ) {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport ((sturmD^[n]) f) :=
  hf.of_isClosed_subset isClosed_closure (sturmD_iterate_tsupport n f)

theorem sturm_compact_mul_integrable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {f g : ℝ → A} (hf : Continuous f) (hc : HasCompactSupport f)
    (hg : ∀ x ∈ tsupport f, ContinuousAt g x) :
    Integrable (fun x => f x * g x) volume := by
  have h : Continuous (fun x => f x * g x) := by
    apply continuous_of_tsupport
    intro x hx
    exact hf.continuousAt.mul (hg x (tsupport_mul_subset_left hx))
  exact h.integrable_of_hasCompactSupport hc.mul_right

theorem sturmPair_integrable {f J : ℝ → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (hJ : ∀ x ∈ Ioi (0 : ℝ), ContinuousAt J x) :
    Integrable (fun x => f x * J x / (x : ℂ)) volume := by
  have h : Integrable (fun x => f x * (J x / (x : ℂ))) volume :=
    sturm_compact_mul_integrable hf hc (fun x hx => (hJ x (hs hx)).div
      Complex.continuous_ofReal.continuousAt (Complex.ofReal_ne_zero.mpr (hs hx).ne'))
  simpa only [mul_div_assoc] using h

theorem sturmL1_integrable {f : ℝ → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ)) :
    Integrable (fun x => ‖f x‖ / x) volume := by
  have hs' : tsupport (fun x => ‖f x‖) ⊆ tsupport f :=
    tsupport_comp_subset (g := norm) norm_zero f
  have h : Integrable (fun x => ‖f x‖ * x⁻¹) volume :=
    sturm_compact_mul_integrable hf.norm (hc.comp_left norm_zero)
      (fun x hx => continuousAt_inv₀ (hs (hs' hx)).ne')
  simpa only [div_eq_mul_inv] using h

theorem sturmPair_norm_le {f J : ℝ → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (B : ℝ) (hJ : ∀ x ∈ tsupport f, ‖J x‖ ≤ B) :
    ‖sturmPair f J‖ ≤ B * sturmL1 f := by
  unfold sturmPair sturmL1
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le ((sturmL1_integrable hf hc hs).integrableOn.const_mul B)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  by_cases hxf : x ∈ tsupport f
  · rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0,← mul_div_assoc,mul_comm B]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hJ x hxf) (norm_nonneg _)) hx0.le
  · simp only [image_eq_zero_of_notMem_tsupport hxf,zero_mul,zero_div,norm_zero,mul_zero,le_refl]

end
end ArtinMatthews.SourceSturm
