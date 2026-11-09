module

public import ArtinMatthews.MarkedMajorLabelFiniteEnergy


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Finset Set
noncomputable section

/-- Changing the positive normalization scale changes only a unit phase. -/
theorem markedMajorEndpointPolynomial_norm_change_scale {α : Type*}
    (S : Finset α) (A : α → ℂ) (w : α → ℝ) (hw : ∀ i ∈ S, 0 < w i)
    {Z Z' : ℝ} (hZ : 0 < Z) (hZ' : 0 < Z') (t : ℝ) :
    ‖markedMajorEndpointPolynomial S A (fun i => w i/Z) t‖ =
      ‖markedMajorEndpointPolynomial S A (fun i => w i/Z') t‖ := by
  rw [markedMajorEndpointPolynomial_scale S A w hw hZ,
    markedMajorEndpointPolynomial_scale S A w hw hZ',norm_mul,norm_mul,
    markedMajor_scale_phase_norm,markedMajor_scale_phase_norm,one_mul]

theorem markedMajorComparable_compact {lo hi Y X X' w : ℝ}
    (hlo : 0 < lo) (hY : 0 < Y) (hX : 0 < X) (hX' : 0 < X')
    (hlow : X ≤ 2*X') (hupp : X' ≤ 2*X) (hw : w/(Y*X') ∈ Icc lo (4*hi)) :
    w/(Y*X) ∈ Icc (lo/2) (8*hi) := by
  have hhi : 0 ≤ hi := by linarith [hw.1,hw.2]
  have hratio : (1/2:ℝ) ≤ X'/X := (le_div_iff₀ hX).mpr (by linarith)
  have hratio' : X'/X ≤ 2 := (div_le_iff₀ hX).mpr hupp
  have he : w/(Y*X) = (X'/X)*(w/(Y*X')) := by field_simp
  rw [he]
  constructor
  · have h := mul_le_mul hratio hw.1 hlo.le (div_nonneg hX'.le hX.le)
    nlinarith
  · have h := mul_le_mul hratio' hw.2 (hlo.le.trans hw.1) (by norm_num : (0:ℝ) ≤ 2)
    nlinarith

/-- An explicit constant-four normalization allowance handles independently
normalized endpoints whose product scales differ by at most two. -/
theorem markedMajorComparable_normalized_bound {X Y I : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {S : ℂ} (hS : ‖S‖ ≤ ((2*Y*X)^2/X)*I) :
    ‖(Y:ℂ)⁻¹*S‖ ≤ (4*Y*X)*I := by
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY]
  calc
    _ ≤ Y⁻¹*(((2*Y*X)^2/X)*I) := mul_le_mul_of_nonneg_left hS (inv_nonneg.mpr hY.le)
    _ = _ := by field_simp; ring

end
end ArtinMatthews
