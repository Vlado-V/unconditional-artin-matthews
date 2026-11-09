module

public import ArtinMatthews.PrimeExtractionMellinBilinear
public import ArtinMatthews.GiantSamplingBilinearRows


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory OAI.SevenEighths
open scoped BigOperators FourierTransform SchwartzMap ContDiff
noncomputable section

def shiftedRawThetaBilinear (η : HeckeFamily.Character) (A B : Finset ℕ)
    (α β : ℕ → ℂ) : ℂ :=
  ∑ m ∈ A, ∑ n ∈ B, α m * β n * idealThetaCoeff η (m * n + 1)

theorem giantCubicSamplingBilinear_mellin_transfer (Φ : ℝ → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ) (hsupp : Function.support Φ ⊆ Icc (1 : ℝ) 2) :
    ∃ CΦ : ℝ, 0 < CΦ ∧ ∀ (η : HeckeFamily.Character) (x : ℝ), 0 < x →
      ∀ (A B : Finset ℕ) (α β : ℕ → ℂ),
      (∀ m ∈ A, 0 < m) → (∀ n ∈ B, 0 < n) →
      (∀ m ∈ A, ‖α m‖ ≤ 1) → (∀ n ∈ B, ‖β n‖ ≤ 1) →
      ∀ R : ℝ, 0 ≤ R →
      (∀ α' β' : ℕ → ℂ, (∀ m ∈ A, ‖α' m‖ ≤ 1) →
        (∀ n ∈ B, ‖β' n‖ ≤ 1) → ‖shiftedRawThetaBilinear η A B α' β'‖ ≤ R) →
      ‖giantCubicSamplingBilinear η Φ x A B α β‖ ≤ CΦ * R := by
  let Ψ : ℝ → ℂ := fun y => (Φ y : ℂ)
  have hΨ : ContDiff ℝ ∞ Ψ := Complex.ofRealCLM.contDiff.comp hΦ
  have hsΨ : Function.support Ψ ⊆ Icc (1 : ℝ) 2 := by
    intro y hy
    apply hsupp
    simpa only [Ψ, Function.mem_support, ne_eq, Complex.ofReal_eq_zero] using hy
  let F : SchwartzMap ℝ ℂ := 𝓕 (primeExtractionLogProfile Ψ (by norm_num) hsΨ hΨ)
  let CΦ : ℝ := 1 + ∫ t : ℝ, ‖F t‖
  have hmass : 0 ≤ ∫ t : ℝ, ‖F t‖ := integral_nonneg (fun t => norm_nonneg (F t))
  have hCΦ : 0 < CΦ := by
    dsimp only [CΦ]
    linarith
  refine ⟨CΦ, hCΦ, ?_⟩
  intro η x hx A B α β hA hB hα hβ R hR hraw
  let W (m n : ℕ) := α m * β n * idealThetaCoeff η (m * n + 1)
  have hphase (t : ℝ) : ‖primeExtractionBilinearPhaseSum A B W t‖ ≤ R := by
    let α' (m : ℕ) := α m * primeExtractionMellinPhase t m
    let β' (n : ℕ) := β n * primeExtractionMellinPhase t n
    have hα' (m : ℕ) (hm : m ∈ A) : ‖α' m‖ ≤ 1 := by
      simpa only [α', norm_mul, primeExtractionMellinPhase_norm, mul_one] using hα m hm
    have hβ' (n : ℕ) (hn : n ∈ B) : ‖β' n‖ ≤ 1 := by
      simpa only [β', norm_mul, primeExtractionMellinPhase_norm, mul_one] using hβ n hn
    have he : primeExtractionBilinearPhaseSum A B W t = shiftedRawThetaBilinear η A B α' β' := by
      unfold primeExtractionBilinearPhaseSum shiftedRawThetaBilinear
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      dsimp only [W, α', β']
      ring
    rw [he]
    exact hraw α' β' hα' hβ'
  have he : giantCubicSamplingBilinear η Φ x A B α β =
      ∫ t : ℝ, F t * primeExtractionMellinPhase (-t) x * primeExtractionBilinearPhaseSum A B W t := by
    calc
      _ = ∑ m ∈ A, ∑ n ∈ B, W m n * Ψ (((m * n : ℕ) : ℝ) / x) := by
        unfold giantCubicSamplingBilinear
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro n hn
        dsimp only [W, Ψ]
        ring
      _ = _ := primeExtraction_bilinear_mellin Ψ (by norm_num) hsΨ hΨ A B W hx hA hB
  rw [he]
  calc
    _ ≤ ∫ t : ℝ, ‖F t * primeExtractionMellinPhase (-t) x *
        primeExtractionBilinearPhaseSum A B W t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖F t‖ * R := by
      apply integral_mono
        (primeExtraction_bilinear_integrable F A B W hx hA hB).norm
        (F.integrable.norm.mul_const R)
      intro t
      simp only [norm_mul, primeExtractionMellinPhase_norm, mul_one]
      exact mul_le_mul_of_nonneg_left (hphase t) (norm_nonneg _)
    _ = (∫ t : ℝ, ‖F t‖) * R := integral_mul_const R _
    _ ≤ CΦ * R := by
      apply mul_le_mul_of_nonneg_right _ hR
      dsimp only [CΦ]
      linarith

end
end ArtinMatthews
