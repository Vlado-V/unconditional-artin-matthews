module

public import ArtinMatthews.SourceQuadraticB3TailScale


set_option backward.privateInPublic true
@[expose] public section

/-! The aggregate tail keeps the common-ideal factor supplied by the divisor estimate. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

theorem sourceQuadraticB3_weighted_tail_common_bound {M P K δ : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hδ : 0 < δ)
    (hlower : P ^ 2 / M * (M * P) ^ δ ≤ K)
    (hupper : K ≤ M * (M * P) ^ (-δ))
    (C : ℝ) (hC : 0 ≤ C) (g : E) (cols : Finset E) (u : E → ℂ) :
    C * (q g : ℝ) ^ 4 *
        (P * (M ^ (1 - quadraticB3TailLine δ) * P ^ (2 * quadraticB3TailLine δ - 1) *
          K ^ (2 - quadraticB3TailLine δ))) * coeffMass cols u ≤
      C * (q g : ℝ) ^ 4 * M * coeffMass cols u := by
  apply mul_le_mul_of_nonneg_right _ (coeffMass_nonneg _ _)
  exact mul_le_mul_of_nonneg_left
    (quadraticB3_tail_pair_bound hM hP hδ hlower hupper)
    (mul_nonneg hC (pow_nonneg (Nat.cast_nonneg _) 4))

theorem sourceQuadraticB3_weighted_tail_to_block {M P K δ : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hδ : 0 < δ)
    (hlower : P ^ 2 / M * (M * P) ^ δ ≤ K)
    (hupper : K ≤ M * (M * P) ^ (-δ))
    (C : ℝ) (hC : 0 ≤ C) (g : E) (cols : Finset E) (u : E → ℂ) (α : ℝ) :
    C * (q g : ℝ) ^ 4 *
        (P * (M ^ (1 - quadraticB3TailLine δ) * P ^ (2 * quadraticB3TailLine δ - 1) *
          K ^ (2 - quadraticB3TailLine δ))) * coeffMass cols u ≤
      (C * (q g : ℝ) ^ 4 * (M * P) ^ δ *
        (M + P + Real.sqrt M * K ^ (α - 1 / 2) + Real.sqrt (M / K) * P)) *
          coeffMass cols u := by
  have hM0 := zero_lt_one.trans_le hM
  have hP0 := zero_lt_one.trans_le hP
  have hK0 := (quadraticB3_cutoff_range hM hP hδ hlower hupper).1
  have hrest : M ≤ M + P + Real.sqrt M * K ^ (α - 1 / 2) + Real.sqrt (M / K) * P := by
    have hterm : 0 ≤ Real.sqrt M * K ^ (α - 1 / 2) := by positivity
    have hterm' : 0 ≤ Real.sqrt (M / K) * P := by positivity
    linarith
  have hscale : M ≤ (M * P) ^ δ *
      (M + P + Real.sqrt M * K ^ (α - 1 / 2) + Real.sqrt (M / K) * P) := by
    exact hrest.trans (le_mul_of_one_le_left (hM0.le.trans hrest)
      (Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hM hP) hδ.le))
  refine (sourceQuadraticB3_weighted_tail_common_bound F S₀ hM hP hδ
    hlower hupper C hC g cols u).trans ?_
  apply mul_le_mul_of_nonneg_right _ (coeffMass_nonneg _ _)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale
    (mul_nonneg hC (pow_nonneg (Nat.cast_nonneg _) 4))

end
end ArtinMatthews.SourceEulerAssembly
