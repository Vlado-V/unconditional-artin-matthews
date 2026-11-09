module

public import ArtinMatthews.PrimeExtractionRelevantMellin


set_option backward.privateInPublic true
@[expose] public section

/-! An absolute Fourier integral estimate on the literal dyadic
Mellin sums. A phase bound is used only on the integrated interval. -/

namespace ArtinMatthews
noncomputable section
open MeasureTheory Finset
open scoped BigOperators SchwartzMap

def giantSlotMellinSum (X : ℕ) (S : Finset (ℕ×ℕ)) (A : ℕ → ℕ → ℂ)
    (f : SchwartzMap ℝ ℂ) (H x : ℝ) : ℂ :=
  ∑ kl ∈ S,∫ t : ℝ in Set.Icc (-H) H,
    f t * primeExtractionMellinPhase (-t) x *
      primeExtractionBilinearPhaseSum (primeExtractionDyadicBlock X kl.1)
        (primeExtractionDyadicBlock X kl.2) A t

theorem giant_slot_mellin_sum_norm_le (X : ℕ) (S : Finset (ℕ×ℕ)) (A : ℕ → ℕ → ℂ)
    (f : SchwartzMap ℝ ℂ) (H x : ℝ) (B : ℕ×ℕ → ℝ)
    (hB : ∀ kl ∈ S,0 ≤ B kl)
    (hpoint : ∀ kl ∈ S,∀ t ∈ Set.Icc (-H) H,
      ‖primeExtractionBilinearPhaseSum (primeExtractionDyadicBlock X kl.1)
        (primeExtractionDyadicBlock X kl.2) A t‖ ≤ B kl) :
    ‖giantSlotMellinSum X S A f H x‖ ≤ (∫ t : ℝ,‖f t‖)*(∑ kl ∈ S,B kl) := by
  unfold giantSlotMellinSum
  rw [mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro kl hkl
  let M := primeExtractionDyadicBlock X kl.1
  let N := primeExtractionDyadicBlock X kl.2
  let F (t : ℝ) := f t * primeExtractionMellinPhase (-t) x * primeExtractionBilinearPhaseSum M N A t
  have hsum : Continuous (primeExtractionBilinearPhaseSum M N A) := by
    unfold primeExtractionBilinearPhaseSum
    apply continuous_finsetSum
    intro m _
    apply continuous_finsetSum
    intro n _
    exact (continuous_const.mul (primeExtractionMellinPhase_continuous (m:ℝ))).mul
      (primeExtractionMellinPhase_continuous (n:ℝ))
  have hF : Continuous F :=
    (f.continuous.mul ((primeExtractionMellinPhase_continuous x).comp continuous_neg)).mul hsum
  change ‖∫ t : ℝ in Set.Icc (-H) H,F t‖ ≤ (∫ t : ℝ,‖f t‖)*B kl
  calc
    _ ≤ ∫ t : ℝ in Set.Icc (-H) H,‖F t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Set.Icc (-H) H,‖f t‖*B kl := by
      apply setIntegral_mono_on hF.norm.integrableOn_Icc
        (f.integrable.norm.mul_const _).integrableOn measurableSet_Icc
      intro t ht
      simp only [F,norm_mul,primeExtractionMellinPhase_norm,mul_one]
      exact mul_le_mul_of_nonneg_left (hpoint kl hkl t ht) (norm_nonneg _)
    _ ≤ ∫ t : ℝ,‖f t‖*B kl :=
      setIntegral_le_integral (f.integrable.norm.mul_const _)
        (Filter.Eventually.of_forall (fun t => mul_nonneg (norm_nonneg _) (hB kl hkl)))
    _ = _ := integral_mul_const _ _

end
end ArtinMatthews
