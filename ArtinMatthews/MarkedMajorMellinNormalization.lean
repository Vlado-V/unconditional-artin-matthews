module

public import ArtinMatthews.MarkedMajorMellinEndpointSum


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Finset MeasureTheory Complex
noncomputable section

theorem markedMajor_log_phase_div {w Z : ℝ} (hw : 0 < w) (hZ : 0 < Z) (t : ℝ) :
    Complex.exp (I*(t : ℂ)*(Real.log (w/Z) : ℂ)) =
      Complex.exp (-(I*(t : ℂ)*(Real.log Z : ℂ)))*Complex.exp (I*(t : ℂ)*(Real.log w : ℂ)) := by
  rw [Real.log_div hw.ne' hZ.ne',← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem markedMajorEndpointPolynomial_scale {α : Type*} (S : Finset α) (A : α → ℂ)
    (w : α → ℝ) (hw : ∀ i ∈ S, 0 < w i) {Z : ℝ} (hZ : 0 < Z) (t : ℝ) :
    markedMajorEndpointPolynomial S A (fun i => w i/Z) t =
      Complex.exp (-(I*(t : ℂ)*(Real.log Z : ℂ)))*markedMajorEndpointPolynomial S A w t := by
  unfold markedMajorEndpointPolynomial
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [markedMajor_log_phase_div (hw i hi) hZ]
  ring

theorem markedMajorEndpointPolynomial_product_scale {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α → ℂ) (B : β → ℂ) (w : α → ℝ) (w' : β → ℝ)
    (hw : ∀ i ∈ S, 0 < w i) (hw' : ∀ j ∈ T, 0 < w' j)
    {Z : ℝ} (hZ : 0 < Z) (t s : ℝ) :
    markedMajorEndpointPolynomial S A (fun i => w i/Z) t *
      markedMajorEndpointPolynomial T B (fun j => w' j/Z) (s-t) =
      Complex.exp (-(I*(s : ℂ)*(Real.log Z : ℂ))) *
        (markedMajorEndpointPolynomial S A w t*markedMajorEndpointPolynomial T B w' (s-t)) := by
  rw [markedMajorEndpointPolynomial_scale S A w hw hZ,
    markedMajorEndpointPolynomial_scale T B w' hw' hZ]
  calc
    _ = (Complex.exp (-(I*(t : ℂ)*(Real.log Z : ℂ))) *
        Complex.exp (-(I*((s-t : ℝ) : ℂ)*(Real.log Z : ℂ)))) *
        (markedMajorEndpointPolynomial S A w t*markedMajorEndpointPolynomial T B w' (s-t)) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring

theorem markedMajor_scale_phase_norm (Z s : ℝ) :
    ‖Complex.exp (-(I*(s : ℂ)*(Real.log Z : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem markedMajor_XY_normalization {X Y : ℝ} (hX : X ≠ 0) (hY : Y ≠ 0) :
    ((Y*X : ℝ) : ℂ)^2 * (X : ℂ)⁻¹ * (Y : ℂ)⁻¹ = ((Y*X : ℝ) : ℂ) := by
  have hx : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX
  have hy : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY
  push_cast
  field_simp

end
end ArtinMatthews
