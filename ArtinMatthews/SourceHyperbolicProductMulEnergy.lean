module

public import ArtinMatthews.SourceHyperbolicProductEnergy


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem productPartial_mul {f g : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (i : ι) (j : Fin 3) :
    productPartial (fun x => f x*g x) i j p =
      f p*productPartial g i j p+g p*productPartial f i j p := by
  simp only [productPartial, fderiv_fun_mul hf hg, add_apply,
    smul_apply, smul_eq_mul]

private theorem norm_add_sq_le (a b : ℂ) : ‖a+b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  calc
    _ ≤ (‖a‖+‖b‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
    _ ≤ _ := by nlinarith [sq_nonneg (‖a‖-‖b‖)]

theorem productGradientEnergy_mul_le {f g : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    productGradientEnergy (fun x => f x*g x) p ≤
      2*‖f p‖^2*productGradientEnergy g p+2*‖g p‖^2*productGradientEnergy f p := by
  let A := 2*‖f p‖^2
  let B := 2*‖g p‖^2
  have hpoint (i : ι) (j : Fin 3) :
      ‖productPartial (fun x => f x*g x) i j p‖^2 ≤
        A*‖productPartial g i j p‖^2+B*‖productPartial f i j p‖^2 := by
    rw [productPartial_mul hf hg]
    simpa only [A,B,norm_mul,mul_pow,mul_assoc] using
      norm_add_sq_le (f p*productPartial g i j p) (g p*productPartial f i j p)
  unfold productGradientEnergy
  calc
    _ ≤ ∑ i, (p i 2)^2*∑ j : Fin 3,
        (A*‖productPartial g i j p‖^2+B*‖productPartial f i j p‖^2) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun j _ => hpoint i j)) (sq_nonneg _))
    _ = _ := by
      have hsplit (i : ι) :
          (p i 2)^2*∑ j : Fin 3,
            (A*‖productPartial g i j p‖^2+B*‖productPartial f i j p‖^2) =
          A*((p i 2)^2*∑ j : Fin 3, ‖productPartial g i j p‖^2)+
            B*((p i 2)^2*∑ j : Fin 3, ‖productPartial f i j p‖^2) := by
        simp only [Finset.sum_add_distrib,← Finset.mul_sum]
        ring
      simp_rw [hsplit]
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,A,B]

end
end ArtinMatthews.SourceHyperbolicGreen
