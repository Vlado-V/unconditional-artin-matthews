module

public import ArtinMatthews.QuadraticHeckeSquareMellin
public import ArtinMatthews.QuadraticHeckePositivePrincipalShift
public import ArtinMatthews.QuadraticHeckePrincipalNormSeries
public import ArtinMatthews.QuadraticHeckeNormSmoothing


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Complex Set MeasureTheory VaryingKummerAnalytic SourcePhysical
open OAI.SevenEighths.ProbePhysical
open scoped NumberField ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (w : ℝ → ℂ)

theorem quadraticHeckeSquareMellin_smooth_verticalIntegrable
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w) (σ : ℝ) :
    Integrable (fun t : ℝ => quadraticHeckeSquareMellin (mellin w)
      ((σ : ℂ) + (t : ℂ) * I)) := by
  let f (t : ℝ) := mellin w ((σ / 2 : ℝ) + (t : ℂ) * I)
  have hf : Integrable f := smoothMellin_verticalIntegrable w hc hp hs (σ / 2)
  have hscaled := hf.comp_mul_left' (by norm_num : (1 / 2 : ℝ) ≠ 0)
  apply (hscaled.const_mul (1 / 2 : ℂ)).congr
  filter_upwards with t
  unfold f quadraticHeckeSquareMellin
  congr 2
  push_cast
  ring

theorem quadraticHeckeSquareMellin_smooth_strip_decay
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    (u v : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, u ≤ s.re → s.re ≤ v →
      (1 + |s.im|) ^ k * ‖quadraticHeckeSquareMellin (mellin w) s‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := smoothMellin_strip_decay w hc hp hs (u / 2) (v / 2) k
  refine ⟨2 ^ k * C, by positivity, ?_⟩
  intro s hlo hhi
  have hhalf := hb (s / 2) (by simp only [div_ofNat_re]; linarith)
    (by simp only [div_ofNat_re]; linarith)
  rw [div_ofNat_im] at hhalf
  have ht : 1 + |s.im| ≤ 2 * (1 + |s.im / 2|) := by
    rw [abs_div]
    norm_num
    linarith [abs_nonneg s.im]
  have hn : ‖quadraticHeckeSquareMellin (mellin w) s‖ ≤ ‖mellin w (s / 2)‖ := by
    rw [quadraticHeckeSquareMellin, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by norm_num)
  calc
    _ ≤ (2 * (1 + |s.im / 2|)) ^ k * ‖mellin w (s / 2)‖ :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) ht _) hn (norm_nonneg _) (by positivity)
    _ = 2 ^ k * ((1 + |s.im / 2|) ^ k * ‖mellin w (s / 2)‖) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hhalf (by positivity)

theorem quadraticHeckeSquareNormContour_right
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {X : ℝ} (hX : 0 < X) :
    (∑' J : {J : Ideal (𝓞 F) // J ≠ ⊥}, w (((Ideal.absNorm J.val : ℝ) / X) ^ 2)) =
      verticalIntegral (5 / 4) (fun s : ℂ => (X : ℂ) ^ s *
        quadraticHeckeSquareMellin (mellin w) s * mixedDedekindZeta F s) := by
  let : Countable {J : Ideal (𝓞 F) // J ≠ ⊥} := quadraticHeckePrincipalIdeal_countable F
  have hcont : Continuous (fun t : ℝ => quadraticHeckeSquareMellin (mellin w)
      (((5 / 4 : ℝ) : ℂ) + (t : ℂ) * I)) := by
    exact ((smoothMellin_entire w hc hp hs.continuous).continuous.comp
      (by fun_prop)).const_mul (1 / 2 : ℂ)
  have h := quadraticHeckeNormSmoothing_contour
    (fun J : {J : Ideal (𝓞 F) // J ≠ ⊥} => (Ideal.absNorm J.val : ℝ))
    (quadraticHeckePrincipalIdealNorm_pos F) (fun _ => 1)
    (quadraticHeckeSquareMellin (mellin w)) (5 / 4) hcont
    (quadraticHeckeSquareMellin_smooth_verticalIntegrable w hc hp hs (5 / 4))
    (by simpa only [norm_one, one_mul] using
      quadraticHeckePrincipalIdealNorm_summable F (σ := 5 / 4) (by norm_num)) hX
  simp only [one_mul] at h
  have hinv (J : {J : Ideal (𝓞 F) // J ≠ ⊥}) :
      mellinInv (5 / 4) (quadraticHeckeSquareMellin (mellin w)) ((Ideal.absNorm J.val : ℝ) / X) =
        w (((Ideal.absNorm J.val : ℝ) / X) ^ 2) := by
    rw [quadraticHeckeSquareMellin_inversion _ _
      (div_pos (quadraticHeckePrincipalIdealNorm_pos F J) hX)]
    exact smoothMellin_inversion w hc hp hs _
      (sq_pos_of_pos (div_pos (quadraticHeckePrincipalIdealNorm_pos F J) hX))
  simp_rw [hinv] at h
  rw [h, verticalIntegral]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  let s : ℂ := ((5 / 4 : ℝ) : ℂ) + (t : ℂ) * I
  have hs' : 1 < s.re := by norm_num [s]
  change _ * _ * (∑' J : {J : Ideal (𝓞 F) // J ≠ ⊥},
      ((Ideal.absNorm J.val : ℝ) : ℂ) ^ (-s)) = _ * _ * mixedDedekindZeta F s
  rw [quadraticHeckePrincipalIdealSeries_eq_zeta F hs', mixedDedekindZeta_eq F hs']

/-- The compact original square norm sum admits the same positive-line
residue decomposition as its Mellin dual. -/
theorem quadraticHeckeSquareNormContour_shift
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {σ X : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hX : 0 < X) :
    (∑' J : {J : Ideal (𝓞 F) // J ≠ ⊥}, w (((Ideal.absNorm J.val : ℝ) / X) ^ 2)) =
      verticalIntegral σ (fun s : ℂ => (X : ℂ) ^ s *
        quadraticHeckeSquareMellin (mellin w) s * mixedDedekindZeta F s) +
        (dedekindZeta_residue F : ℂ) * (X : ℂ) * ((1 / 2 : ℂ) * mellin w (1 / 2)) := by
  rw [quadraticHeckeSquareNormContour_right F w hc hp hs hX]
  have h := quadraticHeckePositivePrincipalShift F (quadraticHeckeSquareMellin (mellin w))
    hσ₀ hσ₁ hX
    (fun s _ => (((smoothMellin_entire w hc hp hs.continuous).differentiableAt.comp s
      (differentiableAt_id.div_const 2)).const_mul (1 / 2 : ℂ)).differentiableWithinAt)
    (quadraticHeckeSquareMellin_smooth_strip_decay w hc hp hs σ (5 / 4))
  simpa only [quadraticHeckeSquareMellin, one_div] using h

end
end ArtinMatthews
