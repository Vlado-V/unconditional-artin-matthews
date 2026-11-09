module

public import ArtinMatthews.SourceHyperbolicProductIMS
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv


set_option backward.privateInPublic true
@[expose] public section

/-! The exact two-piece cosine/sine localization in the native product gradient. -/
namespace ArtinMatthews.SourceHyperbolicGreen
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem trig_partition_complex_norm_sq (a b d : ℝ) (z w : ℂ) :
    ‖(a : ℂ)*z + ((-b*d : ℝ) : ℂ)*w‖ ^ 2 +
      ‖(b : ℂ)*z + ((a*d : ℝ) : ℂ)*w‖ ^ 2 =
        (a^2+b^2)*(‖z‖^2+d^2*‖w‖^2) := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem productGradientEnergy_trig_partition
    {η : ProductSpace ι → ℝ} {f : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hη : DifferentiableAt ℝ η p) (hf : DifferentiableAt ℝ f p) (c : ℝ) :
    productGradientEnergy (fun x => (Real.cos (c*(1-η x)) : ℂ)*f x) p +
      productGradientEnergy (fun x => (Real.sin (c*(1-η x)) : ℂ)*f x) p =
        productGradientEnergy f p +
          c^2 * ‖f p‖^2 * productGradientEnergy (fun x => (η x : ℂ)) p := by
  let θ : ProductSpace ι → ℝ := fun x => c*(1-η x)
  let A : ProductSpace ι → ℝ := fun x => Real.cos (θ x)
  let B : ProductSpace ι → ℝ := fun x => Real.sin (θ x)
  have h1 : DifferentiableAt ℝ (fun _ : ProductSpace ι => (1 : ℝ)) p := differentiableAt_const 1
  have hθ : DifferentiableAt ℝ θ p := (h1.sub hη).const_mul c
  have hA : DifferentiableAt ℝ A p := Real.differentiable_cos.differentiableAt.comp p hθ
  have hB : DifferentiableAt ℝ B p := Real.differentiable_sin.differentiableAt.comp p hθ
  have ha : DifferentiableAt ℝ (fun x => (A x : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p hA
  have hb : DifferentiableAt ℝ (fun x => (B x : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p hB
  have hab : A p^2+B p^2 = 1 := Real.cos_sq_add_sin_sq (θ p)
  have hθd (i : ι) (j : Fin 3) :
      fderiv ℝ θ p (productDirection i j) = -c * fderiv ℝ η p (productDirection i j) := by
    change fderiv ℝ (fun x => c * (((fun _ : ProductSpace ι => (1 : ℝ)) - η) x)) p
      (productDirection i j) = _
    rw [fderiv_const_mul (h1.sub hη) c, fderiv_sub h1 hη]
    rw [fderiv_const_apply,zero_sub]
    change c * (-(fderiv ℝ η p (productDirection i j))) = _
    ring
  have hlocal (i : ι) (j : Fin 3) :
      ‖productPartial (fun x => (A x : ℂ)*f x) i j p‖^2 +
        ‖productPartial (fun x => (B x : ℂ)*f x) i j p‖^2 =
          ‖productPartial f i j p‖^2 +
            (c^2*‖f p‖^2)*‖productPartial (fun x => (η x : ℂ)) i j p‖^2 := by
    let d := fderiv ℝ θ p (productDirection i j)
    have hAd : productPartial (fun x => (A x : ℂ)) i j p = ((-B p*d : ℝ) : ℂ) := by
      rw [productPartial_ofReal hA]
      change ((fderiv ℝ (fun x => Real.cos (θ x)) p (productDirection i j) : ℝ) : ℂ) = _
      rw [fderiv_cos hθ]
      rfl
    have hBd : productPartial (fun x => (B x : ℂ)) i j p = ((A p*d : ℝ) : ℂ) := by
      rw [productPartial_ofReal hB]
      change ((fderiv ℝ (fun x => Real.sin (θ x)) p (productDirection i j) : ℝ) : ℂ) = _
      rw [fderiv_sin hθ]
      rfl
    rw [productPartial_mul ha hf,productPartial_mul hb hf,hAd,hBd]
    rw [mul_comm (f p) (((-B p*d : ℝ) : ℂ)),mul_comm (f p) (((A p*d : ℝ) : ℂ))]
    rw [trig_partition_complex_norm_sq,hab,one_mul,productPartial_ofReal hη]
    dsimp only [d]
    rw [hθd,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    ring
  have hblock (i : ι) :
      (p i 2)^2 * ∑ j : Fin 3, ‖productPartial (fun x => (A x : ℂ)*f x) i j p‖^2 +
        (p i 2)^2 * ∑ j : Fin 3, ‖productPartial (fun x => (B x : ℂ)*f x) i j p‖^2 =
          (p i 2)^2 * (∑ j : Fin 3, ‖productPartial f i j p‖^2) +
            (c^2*‖f p‖^2)*((p i 2)^2 *
              ∑ j : Fin 3, ‖productPartial (fun x => (η x : ℂ)) i j p‖^2) := by
    rw [← mul_add,← Finset.sum_add_distrib]
    simp_rw [hlocal i]
    rw [Finset.sum_add_distrib,← Finset.mul_sum]
    ring
  change productGradientEnergy (fun x => (A x : ℂ)*f x) p +
    productGradientEnergy (fun x => (B x : ℂ)*f x) p = _
  unfold productGradientEnergy
  rw [← Finset.sum_add_distrib]
  simp_rw [hblock]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]

end
end ArtinMatthews.SourceHyperbolicGreen
