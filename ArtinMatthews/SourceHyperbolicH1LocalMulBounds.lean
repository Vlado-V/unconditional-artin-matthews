module

public import ArtinMatthews.SourceHyperbolicProductMulEnergy
public import ArtinMatthews.SourceHyperbolicH1LocalMassNorm


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open MeasureTheory
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem h1LocalTest_gradient_norm_sq (U : Set (ProductSpace ι)) (f : h1LocalTests U) :
    ‖h1TestGradient f.val‖^2 = ∫ x in U, productGradientEnergy f.val.val x ∂productVolume ι := by
  rw [h1TestGradient_norm_sq]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hzero (i : ι) (j : Fin 3) : productPartial f.val.val i j x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (f.prop (product_test_partial_support i j h)))
  simp [productGradientEnergy,hzero]

end
end ArtinMatthews.SourceHyperbolicGreen

namespace ArtinMatthews
open MeasureTheory Filter SourceHyperbolicGreen
open scoped Topology ContDiff
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem h1LocalTestMul_gradient_norm_sq_le
    (U : Set (ProductSpace ι)) (hU : IsOpen U) (hUupper : U ⊆ productUpper ι)
    (η : h1LocalTests U) (F : ProductSpace ι → ℂ) (hF : ContDiffOn ℝ 2 F U)
    (M B : ℝ) (hη : ∀ x ∈ U, ‖η.val.val x‖ ≤ M)
    (hEη : ∀ x ∈ U, productGradientEnergy η.val.val x ≤ B)
    (hMassInt : IntegrableOn (fun x => ‖F x‖^2) U (productVolume ι))
    (hGradInt : IntegrableOn (productGradientEnergy F) U (productVolume ι)) :
    ‖h1TestGradient (h1LocalTestMul U hU hUupper η F hF).val‖^2 ≤
      2*(M^2*(∫ x in U, productGradientEnergy F x ∂productVolume ι)+
        B*(∫ x in U, ‖F x‖^2 ∂productVolume ι)) := by
  let g := h1LocalTestMul U hU hUupper η F hF
  have hLocal := productGradientEnergy_integrable g.val.prop.1 g.val.prop.2.1 g.val.prop.2.2
  have hGrad := hGradInt.const_mul (M^2)
  have hMass := hMassInt.const_mul B
  have hRhs : IntegrableOn (fun x => 2*(M^2*productGradientEnergy F x+B*‖F x‖^2))
      U (productVolume ι) := (hGrad.add hMass).const_mul 2
  calc
    _ = ∫ x in U, productGradientEnergy g.val.val x ∂productVolume ι :=
      h1LocalTest_gradient_norm_sq U g
    _ ≤ ∫ x in U, 2*(M^2*productGradientEnergy F x+B*‖F x‖^2) ∂productVolume ι := by
      apply integral_mono_ae hLocal.integrableOn hRhs
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      have hdiffη := η.val.prop.1.differentiable (by norm_num) x
      have hdiffF := ((hF x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
      have hprod := productGradientEnergy_mul_le hdiffη hdiffF
      have hfirst := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hη x hx) 2) (productGradientEnergy_nonneg F x)
      have hsecond := mul_le_mul_of_nonneg_right (hEη x hx) (sq_nonneg ‖F x‖)
      change productGradientEnergy (fun p => η.val.val p*F p) x ≤ _
      nlinarith only [hprod,hfirst,hsecond]
    _ = _ := by rw [integral_const_mul,integral_add hGrad hMass,integral_const_mul,integral_const_mul]

theorem h1LocalTestMul_energy_norm_sq_le
    (U : Set (ProductSpace ι)) (hU : IsOpen U) (hUupper : U ⊆ productUpper ι)
    (η : h1LocalTests U) (F : ProductSpace ι → ℂ) (hF : ContDiffOn ℝ 2 F U)
    (M B : ℝ) (hη : ∀ x ∈ U, ‖η.val.val x‖ ≤ M)
    (hEη : ∀ x ∈ U, productGradientEnergy η.val.val x ≤ B)
    (hMassInt : IntegrableOn (fun x => ‖F x‖^2) U (productVolume ι))
    (hGradInt : IntegrableOn (productGradientEnergy F) U (productVolume ι)) :
    ‖h1EnergyCore (h1LocalTestMul U hU hUupper η F hF).val‖^2 ≤
      (M^2+2*B)*(∫ x in U, ‖F x‖^2 ∂productVolume ι)+
        2*M^2*(∫ x in U, productGradientEnergy F x ∂productVolume ι) := by
  rw [h1Energy_norm_sq,h1EnergyMass_core,h1EnergyGradient_core]
  have hm := h1LocalTestMul_mass_norm_sq_le U hU hUupper η F hF M hη hMassInt
  have hg := h1LocalTestMul_gradient_norm_sq_le U hU hUupper η F hF M B hη hEη hMassInt hGradInt
  nlinarith only [hm,hg]

end
end ArtinMatthews
