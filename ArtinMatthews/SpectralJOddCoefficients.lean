module

public import ArtinMatthews.SpectralJIntegerSeries
public import ArtinMatthews.SpectralKLPhysicalCompactData


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

def spectralJDiscreteCoefficient (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (f x / (x : ℂ)) * Complex.besselJ (n : ℂ) (x : ℂ)

theorem spectralJDiscreteCoefficient_norm_le (f : ℝ → ℂ) (n : ℕ)
    (R : ℝ) (hR : 0 ≤ R) (hs : ∀ x ∈ tsupport f, x ≤ R)
    (hi : IntegrableOn (fun x : ℝ => f x / (x : ℂ)) (Ioi (0 : ℝ))) :
    ‖spectralJDiscreteCoefficient f n‖ ≤
      ((R / 2) ^ n / (n.factorial : ℝ) * Real.exp (R ^ 2 / 4)) *
        ∫ x in Ioi (0 : ℝ), ‖f x / (x : ℂ)‖ := by
  unfold spectralJDiscreteCoefficient
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ),
        ((R / 2) ^ n / (n.factorial : ℝ) * Real.exp (R ^ 2 / 4)) *
          ‖f x / (x : ℂ)‖ := by
      apply norm_integral_le_of_norm_le (hi.norm.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      change 0 < x at hx
      by_cases hf : f x = 0
      · simp only [hf, zero_div, zero_mul, norm_zero, mul_zero, le_refl]
      · have hxR : x ≤ R := hs x (subset_tsupport f hf)
        have hJ : ‖Complex.besselJ (n : ℂ) (x : ℂ)‖ ≤
            (R / 2) ^ n / (n.factorial : ℝ) * Real.exp (R ^ 2 / 4) := by
          refine (spectral_besselJ_nat_norm_le_real n x hx.le).trans ?_
          have hsq : x ^ 2 ≤ R ^ 2 := (sq_le_sq₀ hx.le hR).mpr hxR
          gcongr
        rw [norm_mul]
        calc
          _ ≤ ‖f x / (x : ℂ)‖ *
              ((R / 2) ^ n / (n.factorial : ℝ) * Real.exp (R ^ 2 / 4)) :=
            mul_le_mul_of_nonneg_left hJ (norm_nonneg _)
          _ = _ := mul_comm _ _
    _ = _ := integral_const_mul _ _

theorem spectralJDiscreteCoefficient_factorial_bound (f : ℝ → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi (0 : ℝ)) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ n : ℕ,
      ‖spectralJDiscreteCoefficient f n‖ ≤ C * A ^ n / (n.factorial : ℝ) := by
  obtain ⟨R, hR⟩ := hfc.bddAbove
  let B : ℝ := max 1 R
  have hB : 0 ≤ B := le_trans zero_le_one (le_max_left _ _)
  have hs : ∀ x ∈ tsupport f, x ≤ B := fun x hx => (hR hx).trans (le_max_right _ _)
  have hi : IntegrableOn (fun x : ℝ => f x / (x : ℂ)) (Ioi (0 : ℝ)) :=
    (spectralKLPhysicalCompactDiv_integrable f hf hfc hpos).restrict
  let I : ℝ := ∫ x in Ioi (0 : ℝ), ‖f x / (x : ℂ)‖
  refine ⟨Real.exp (B ^ 2 / 4) * I, B / 2,
    mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _),
    by positivity, ?_⟩
  intro n
  calc
    _ ≤ ((B / 2) ^ n / (n.factorial : ℝ) * Real.exp (B ^ 2 / 4)) * I :=
      spectralJDiscreteCoefficient_norm_le f n B hB hs hi
    _ = _ := by ring

end
end ArtinMatthews
