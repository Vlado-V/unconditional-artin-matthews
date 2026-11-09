module

public import ArtinMatthews.QuadraticB3TailScale
public import ArtinMatthews.SourceQuadraticPairConductor


set_option backward.privateInPublic true
@[expose] public section

/-! The scalar tail estimate with the actual common-ideal factor and B3 energy mass. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

theorem sourceQuadraticB3_tail_common_bound {M P K δ : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hδ : 0 < δ)
    (hlower : P ^ 2 / M * (M * P) ^ δ ≤ K)
    (hupper : K ≤ M * (M * P) ^ (-δ))
    (C : ℝ) (hC : 0 ≤ C) (g : E) (cols : Finset E) (u : E → ℂ) :
    C * (P * (M ^ (1 - quadraticB3TailLine δ) * P ^ (2 * quadraticB3TailLine δ - 1) *
        K ^ (2 - quadraticB3TailLine δ))) * coeffMass cols u ≤
      C * (q g : ℝ) ^ 4 * M * coeffMass cols u := by
  have hg : 1 ≤ (q g : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (sourcePrimeExponentNorm_pos F S₀ g).ne'
  have hg4 : 1 ≤ (q g : ℝ) ^ 4 := one_le_pow₀ hg
  apply mul_le_mul_of_nonneg_right _ (coeffMass_nonneg _ _)
  calc
    _ ≤ C * M := mul_le_mul_of_nonneg_left
      (quadraticB3_tail_pair_bound hM hP hδ hlower hupper) hC
    _ ≤ C * (q g : ℝ) ^ 4 * M := by
      exact mul_le_mul_of_nonneg_right
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hg4 hC)
        (zero_le_one.trans hM)

theorem sourceQuadraticB3_tail_to_block {M P K δ : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hδ : 0 < δ)
    (hlower : P ^ 2 / M * (M * P) ^ δ ≤ K)
    (hupper : K ≤ M * (M * P) ^ (-δ))
    (C : ℝ) (hC : 0 ≤ C) (g : E) (cols : Finset E) (u : E → ℂ) (α : ℝ) :
    C * (P * (M ^ (1 - quadraticB3TailLine δ) * P ^ (2 * quadraticB3TailLine δ - 1) *
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
  refine (sourceQuadraticB3_tail_common_bound F S₀ hM hP hδ hlower hupper C hC g cols u).trans ?_
  apply mul_le_mul_of_nonneg_right _ (coeffMass_nonneg _ _)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale
    (mul_nonneg hC (pow_nonneg (Nat.cast_nonneg _) 4))

end
end ArtinMatthews.SourceEulerAssembly
