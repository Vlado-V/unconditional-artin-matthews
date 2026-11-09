module

public import ArtinMatthews.MarkedMajorMellinEnergyAssembly
public import ArtinMatthews.MarkedMajorMellinNormalization


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set Finset
noncomputable section

/-- Actual finite compact endpoints inherit the L1 estimate with exactly Z²/X.
The endpoint norm hypotheses accommodate the exact unit-modulus scaling phase. -/
theorem markedMajor_finite_endpoint_L1_bound {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α → ℂ) (B : β → ℂ) (w : α → ℝ) (w' : β → ℝ)
    (ψ : SchwartzMap ℝ ℂ) {a b R X Z : ℝ} (ha : 0 < a) (hab : a < b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (hX : 0 < X) (hZ : 0 ≤ Z) (theta : ℝ)
    (hw : ∀ i ∈ S, w i ∈ Icc a b) (hw' : ∀ j ∈ T, w' j ∈ Icc a b)
    (Q Q' : ℝ → ℂ) (hQ : Continuous Q) (hQ' : Continuous Q')
    (hBQ : ∃ K, ∀ t, ‖Q t‖ ≤ K) (hBQ' : ∃ K', ∀ t, ‖Q' t‖ ≤ K')
    (hP : ∀ t, ‖markedMajorEndpointPolynomial S A w t‖ ≤ Z*‖Q t‖)
    (hP' : ∀ t, ‖markedMajorEndpointPolynomial T B w' t‖ ≤ Z*‖Q' t‖) :
    ‖∑ i ∈ S, ∑ j ∈ T, (A i*B j)*(ψ (X*(w i-w' j))*
      OAI.Problem337.RealPhase.phase (theta*(X*(w i-w' j))))‖ ≤
      (Z^2/X)*(∫ p : ℝ × ℝ, ‖markedMajorConstructedCoefficient ψ ha hab hψ hX theta (p.1/X,p.2)*
        (Q p.1*Q' (p.2-p.1))‖) := by
  let F := markedMajorConstructedCoefficient ψ ha hab hψ hX theta
  let f := fun p : ℝ × ℝ => F (p.1/X,p.2)*
    (markedMajorEndpointPolynomial S A w p.1*markedMajorEndpointPolynomial T B w' (p.2-p.1))
  let g := fun p : ℝ × ℝ => F (p.1/X,p.2)*(Q p.1*Q' (p.2-p.1))
  have hf : Integrable f := markedMajor_mellin_endpoint_integrable S T A B w w'
    (fun i hi => ha.trans_le (hw i hi).1) (fun j hj => ha.trans_le (hw' j hj).1)
    (markedMajorConstructedKernel ψ ha hab hψ hX theta) hX
  obtain ⟨K,hK⟩ := hBQ
  obtain ⟨K',hK'⟩ := hBQ'
  have hg : Integrable g := markedMajor_scaled_endpoint_integrable F hX Q Q' hQ hQ' hK hK'
  have hp (p : ℝ × ℝ) : ‖f p‖ ≤ Z^2*‖g p‖ := by
    have h := mul_le_mul (hP p.1) (hP' (p.2-p.1)) (norm_nonneg _)
      (mul_nonneg hZ (norm_nonneg _))
    have H := mul_le_mul_of_nonneg_left h (norm_nonneg (F (p.1/X,p.2)))
    dsimp [f,g]
    simp only [norm_mul]
    convert H using 1
    ring
  have H := integral_mono hf.norm (hg.norm.const_mul (Z^2)) hp
  rw [integral_const_mul] at H
  rw [markedMajor_constructed_finite_endpoints S T A B w w' ψ ha hab hψ hX theta hw hw',
    norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hX]
  calc
    _ ≤ X⁻¹*(∫ p, ‖f p‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.mpr hX.le)
    _ ≤ X⁻¹*(Z^2*(∫ p, ‖g p‖)) := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hX.le)
    _ = _ := by dsimp [g,F]; rw [div_eq_mul_inv]; ring

theorem markedMajor_scaled_polynomial_norm {α : Type*} (S : Finset α) (A : α → ℂ)
    (w : α → ℝ) (hw : ∀ i ∈ S, 0 < w i) {Z : ℝ} (hZ : 0 < Z)
    (Q : ℝ → ℂ) (he : ∀ t, markedMajorEndpointPolynomial S A w t = (Z:ℂ)*Q t) (t : ℝ) :
    ‖markedMajorEndpointPolynomial S A (fun i => w i/Z) t‖ = Z*‖Q t‖ := by
  rw [markedMajorEndpointPolynomial_scale S A w hw hZ,he,norm_mul,
    markedMajor_scale_phase_norm,one_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hZ]

/-- The source's outer Y⁻¹ normalization leaves exactly YX. -/
theorem markedMajor_normalized_endpoint_bound {X Y I : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {S : ℂ} (hS : ‖S‖ ≤ ((Y*X)^2/X)*I) :
    ‖(Y:ℂ)⁻¹*S‖ ≤ (Y*X)*I := by
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY]
  calc
    _ ≤ Y⁻¹*(((Y*X)^2/X)*I) := mul_le_mul_of_nonneg_left hS (inv_nonneg.mpr hY.le)
    _ = _ := by field_simp

end
end ArtinMatthews
