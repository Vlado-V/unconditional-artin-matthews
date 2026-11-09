module

public import ArtinMatthews.PrimeExtractionRelevantBoxes


set_option backward.privateInPublic true
@[expose] public section

/-! Mellin truncation on the exact boxes whose lower endpoints and product
scale meet the marked bilinear criterion. -/

noncomputable section
namespace ArtinMatthews

open Filter MeasureTheory OAI.SevenEighths
open scoped BigOperators FourierTransform SchwartzMap ContDiff

theorem prime_extraction_dyadic_subset_mellin_error (Φ : ℝ → ℂ) {a b : ℝ}
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) (hΦ : ContDiff ℝ ∞ Φ)
    (N : ℕ) (A : ℕ → ℕ → ℂ) (S : Finset (ℕ × ℕ))
    (hS : S ⊆ primeExtractionDyadicActive N) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ m n, ‖A m n‖ ≤ C) (k : ℕ) {H x : ℝ} (hH : 0 < H) (hx : 0 < x) :
    ‖(∑ kl ∈ S, ∑ m ∈ primeExtractionDyadicBlock N kl.1,
        ∑ n ∈ primeExtractionDyadicBlock N kl.2, A m n * Φ (((m*n : ℕ) : ℝ)/x)) -
      ∑ kl ∈ S, ∫ t : ℝ in Set.Icc (-H) H,
        (𝓕 (primeExtractionLogProfile Φ ha hsupp hΦ)) t * primeExtractionMellinPhase (-t) x *
          primeExtractionBilinearPhaseSum (primeExtractionDyadicBlock N kl.1)
            (primeExtractionDyadicBlock N kl.2) A t‖ ≤
      ((∫ t : ℝ, |t|^k * ‖(𝓕 (primeExtractionLogProfile Φ ha hsupp hΦ)) t‖) / H^k) *
        C*N*(1+Real.log (N+1)/Real.log 2)^2 := by
  let f : SchwartzMap ℝ ℂ := 𝓕 (primeExtractionLogProfile Φ ha hsupp hΦ)
  let D := (∫ t : ℝ, |t|^k * ‖f t‖) / H^k
  have hD : 0 ≤ D := div_nonneg
    (integral_nonneg (fun t => mul_nonneg (pow_nonneg (abs_nonneg t) _) (norm_nonneg _)))
    (pow_pos hH _).le
  have hpos (l : ℕ) : ∀ n ∈ primeExtractionDyadicBlock N l, 0 < n := by
    intro n hn
    exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ kl ∈ S, ‖(∑ m ∈ primeExtractionDyadicBlock N kl.1,
        ∑ n ∈ primeExtractionDyadicBlock N kl.2, A m n * Φ (((m*n : ℕ) : ℝ)/x)) -
      ∫ t : ℝ in Set.Icc (-H) H, f t * primeExtractionMellinPhase (-t) x *
        primeExtractionBilinearPhaseSum (primeExtractionDyadicBlock N kl.1)
          (primeExtractionDyadicBlock N kl.2) A t‖ := norm_sum_le _ _
    _ ≤ ∑ kl ∈ S, D * primeExtractionBilinearMass
        (primeExtractionDyadicBlock N kl.1) (primeExtractionDyadicBlock N kl.2) A := by
      apply Finset.sum_le_sum
      intro kl _
      exact primeExtraction_bilinear_mellin_truncation Φ ha hsupp hΦ _ _ _ k hH hx
        (hpos _) (hpos _)
    _ = D * ∑ kl ∈ S, primeExtractionBilinearMass
        (primeExtractionDyadicBlock N kl.1) (primeExtractionDyadicBlock N kl.2) A :=
      (Finset.mul_sum ..).symm
    _ ≤ D * ∑ kl ∈ primeExtractionDyadicActive N, primeExtractionBilinearMass
        (primeExtractionDyadicBlock N kl.1) (primeExtractionDyadicBlock N kl.2) A :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hS
        (fun kl _ _ => primeExtractionBilinearMass_nonneg _ _ _)) hD
    _ ≤ D * (C*N*(1+Real.log (N+1)/Real.log 2)^2) :=
      mul_le_mul_of_nonneg_left (primeExtractionDyadicTotal_mass_le N A hC
        (fun _ _ m _ n _ => hA m n)) hD
    _ = _ := by dsimp [D, f]; ring

def markedExtractionRelevantMellin {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) {a T : ℝ}
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a T) (hΦ : ContDiff ℝ ∞ Φ)
    (γ : ℝ) (j : ℕ) (H x : ℝ) : ℂ :=
  ∑ kl ∈ primeExtractionRelevantBoxes ⌊T*x⌋₊ a γ x,
    ∫ t : ℝ in Set.Icc (-H) H,
      (𝓕 (primeExtractionRealLogProfile Φ ha hsupp hΦ)) t *
        primeExtractionMellinPhase (-t) x *
          primeExtractionBilinearPhaseSum (primeExtractionDyadicBlock ⌊T*x⌋₊ kl.1)
            (primeExtractionDyadicBlock ⌊T*x⌋₊ kl.2)
            (markedExtractionBilinearCoefficient e η χ G γ j x) t

theorem markedExtractionRelevantMellin_error {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i) (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    {CG : ℝ} (hCG : 0 ≤ CG) (hG : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) {a T : ℝ} (ha : 0 < a)
    (hsupp : Function.support Φ ⊆ Set.Icc a T) (hΦ : ContDiff ℝ ∞ Φ)
    (γ : ℝ) {j : ℕ} (hj : 2 ≤ j) (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ H : ℝ, 0 < H →
      ‖markedDirectTupleThetaSum e η χ G Φ T γ j x -
        markedExtractionRelevantMellin e η χ G Φ ha hsupp hΦ γ j H x‖ ≤
      ((∫ t : ℝ, |t|^k * ‖(𝓕 (primeExtractionRealLogProfile Φ ha hsupp hΦ)) t‖) / H^k) *
        ((2 / Real.log 2)^Fintype.card ι * CG * (2 : ℝ)^j) * (⌊T*x⌋₊ : ℝ) *
          (1+Real.log ((⌊T*x⌋₊ : ℝ)+1)/Real.log 2)^2 := by
  filter_upwards [markedExtractionBilinearCoefficient_bound e he η χ G hCG hG γ (by omega : 1 ≤ j),
    eventually_gt_atTop (0 : ℝ)] with x hA hx
  intro H hH
  rw [markedDirectTupleThetaSum_relevant e η χ G Φ hsupp hx γ hj]
  exact prime_extraction_dyadic_subset_mellin_error (fun y => (Φ y : ℂ)) ha
    (primeExtraction_complexCutoff_support Φ hsupp) (Complex.ofRealCLM.contDiff.comp hΦ)
    _ _ _ (primeExtractionRelevantBoxes_subset _ _ _ _) (by positivity) hA k hH hx

end ArtinMatthews
