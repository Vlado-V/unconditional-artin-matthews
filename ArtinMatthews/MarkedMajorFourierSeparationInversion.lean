module

public import ArtinMatthews.MarkedMajorFourierSeparationBase


set_option backward.privateInPublic true
@[expose] public section

/-! Exact positive-exponential inversion with the full planar Jacobian. -/
namespace ArtinMatthews
open MeasureTheory Complex
open scoped FourierTransform SchwartzMap
noncomputable section

def markedMajorFourierPhase (p x : ℝ × ℝ) : ℂ :=
  Complex.exp (((p.1*x.1+p.2*x.2 : ℝ) : ℂ)*I)

@[simp] theorem markedMajorFourierPhase_norm (p x : ℝ × ℝ) :
    ‖markedMajorFourierPhase p x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem markedMajorFourierCoefficient_phase_integrable
    (g : SchwartzMap (ℝ × ℝ) ℂ) (x : ℝ × ℝ) :
    Integrable (fun p => markedMajorFourierCoefficient g p * markedMajorFourierPhase p x) := by
  apply (markedMajorFourierCoefficient g).integrable.mul_bdd (c := 1)
  · apply Continuous.aestronglyMeasurable
    unfold markedMajorFourierPhase
    fun_prop
  · exact Filter.Eventually.of_forall (fun p => le_of_eq (markedMajorFourierPhase_norm p x))

theorem markedMajorFourier_inversion (g : SchwartzMap (ℝ × ℝ) ℂ) (x : ℝ × ℝ) :
    g x = ∫ p : ℝ × ℝ, markedMajorFourierCoefficient g p * markedMajorFourierPhase p x := by
  let c : ℝ := 2*Real.pi
  have hc : c ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hcpos : 0 < c := by dsimp [c]; positivity
  let H : (ℝ × ℝ) → ℂ := fun p =>
    markedMajorPlaneFourier g p * markedMajorFourierPhase (c • p) x
  have hbase : g x = ∫ p : ℝ × ℝ, H p := by
    rw [markedMajorPlaneFourier_inverse g x]
    apply integral_congr_ae
    filter_upwards with p
    dsimp [H,markedMajorFourierPhase]
    have he : c*(p.1*x.1+p.2*x.2) = (c*p.1)*x.1+(c*p.2)*x.2 := by ring
    simp only [c] at he ⊢
    rw [← he,mul_comm]
  have hpoint (p : ℝ × ℝ) :
      markedMajorFourierCoefficient g p * markedMajorFourierPhase p x =
        (c^2)⁻¹ • H (c⁻¹ • p) := by
    change (((c^2)⁻¹ : ℝ) • markedMajorPlaneFourier g (c⁻¹ • p)) * markedMajorFourierPhase p x = _
    dsimp [H]
    rw [smul_smul,mul_inv_cancel₀ hc,one_smul]
    exact mul_assoc _ _ _
  rw [show (fun p => markedMajorFourierCoefficient g p * markedMajorFourierPhase p x) =
    (fun p => (c^2)⁻¹ • H (c⁻¹ • p)) from funext hpoint]
  rw [integral_smul,Measure.integral_comp_inv_smul_of_nonneg volume H hcpos.le]
  simp only [Module.finrank_prod,Module.finrank_self,one_add_one_eq_two,
    smul_smul,inv_mul_cancel₀ (pow_ne_zero 2 hc),one_smul]
  exact hbase

theorem markedMajorFourier_inversion_iterated (g : SchwartzMap (ℝ × ℝ) ℂ) (ζ z : ℝ) :
    g (ζ,z) = ∫ v : ℝ, ∫ s : ℝ,
      markedMajorFourierCoefficient g (v,s) * Complex.exp (((v*ζ+s*z : ℝ) : ℂ)*I) := by
  rw [markedMajorFourier_inversion g (ζ,z)]
  exact integral_prod _ (markedMajorFourierCoefficient_phase_integrable g (ζ,z))

end
end ArtinMatthews
