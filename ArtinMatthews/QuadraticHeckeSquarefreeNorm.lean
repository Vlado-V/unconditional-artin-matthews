module

public import ArtinMatthews.SourceQuadraticIdealSquarePart
public import ArtinMatthews.VaryingKummerAnalyticRayIdealMultiplicativity


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField SourceEulerAssembly VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
local notation "J₀" => {J : Ideal (𝓞 K) // J ≠ ⊥}
local notation "SF" => {J : Ideal (𝓞 K) // Squarefree J}

/-- The norm cutoff on the unique squarefree part in the original GL sum. -/
def quadraticHeckeSquarefreeNorm (J : J₀) : ℕ :=
  Ideal.absNorm (sourceQuadraticIdealSquareParts K J).1.val

private theorem quadratic_coefficient_square {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M)
    (hχ : ∀ J : J₀, IsCoprime J.val M → ψ.allCoefficient J.val ^ 2 = 1)
    (b : J₀) : ψ.allCoefficient b.val ^ 2 = if IsCoprime b.val M then 1 else 0 := by
  by_cases hb : IsCoprime b.val M
  · rw [ite_eq_left hb, hχ b hb]
  · simp [EvenIdealRayCharacter.allCoefficient, b.property, hb]

/-- The exact squarefree-part truncation separates into a signed squarefree
coefficient and an unsigned square-ideal norm sum. -/
theorem quadraticHeckeSquarefreeNorm_tsum {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M)
    (hχ : ∀ J : J₀, IsCoprime J.val M → ψ.allCoefficient J.val ^ 2 = 1)
    (m : Ideal (𝓞 K)) (H X : ℝ) (w : ℝ → ℂ)
    (habs : Summable (fun J : J₀ => ‖ψ.allCoefficient J.val *
      w ((Ideal.absNorm J.val : ℝ) / X)‖)) :
    (∑' J : J₀, if IsCoprime J.val m ∧ (quadraticHeckeSquarefreeNorm K J : ℝ) ≤ H then
      ψ.allCoefficient J.val * w ((Ideal.absNorm J.val : ℝ) / X) else 0) =
    ∑' a : SF, if IsCoprime a.val m ∧ (Ideal.absNorm a.val : ℝ) ≤ H then
      ψ.allCoefficient a.val * ∑' b : J₀, if IsCoprime b.val m ∧ IsCoprime b.val M then
        w ((Ideal.absNorm a.val : ℝ) * (Ideal.absNorm b.val : ℝ) ^ 2 / X) else 0
      else 0 := by
  let f (J : J₀) : ℂ :=
    if IsCoprime J.val m ∧ (quadraticHeckeSquarefreeNorm K J : ℝ) ≤ H then
      ψ.allCoefficient J.val * w ((Ideal.absNorm J.val : ℝ) / X) else 0
  have hf : Summable f := by
    apply habs.of_norm_bounded
    intro J
    dsimp only [f]
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg _
  let e := sourceQuadraticIdealSquareParts K
  have he : Summable (fun p : SF × J₀ => f (e.symm p)) := hf.comp_injective e.symm.injective
  change (∑' J : J₀, f J) = _
  rw [← e.symm.tsum_eq f, he.tsum_prod]
  apply tsum_congr
  intro a
  have hJ (b : J₀) : (e.symm (a,b)).val = a.val * b.val ^ 2 :=
    sourceQuadraticIdealSquareParts_symm_val K (a,b)
  have hnorm (b : J₀) : quadraticHeckeSquarefreeNorm K (e.symm (a,b)) = Ideal.absNorm a.val := by
    unfold quadraticHeckeSquarefreeNorm
    change Ideal.absNorm (e (e.symm (a,b))).1.val = _
    rw [Equiv.apply_symm_apply]
  by_cases ha : IsCoprime a.val m ∧ (Ideal.absNorm a.val : ℝ) ≤ H
  · rw [ite_eq_left ha, ← tsum_mul_left]
    apply tsum_congr
    intro b
    simp only [f, hnorm, hJ, pow_two, IsCoprime.mul_left_iff, and_self, ha.1,
      ha.2, true_and, and_true, map_mul, Nat.cast_mul, ψ.allCoefficient_mul]
    rw [← pow_two (ψ.allCoefficient b.val), quadratic_coefficient_square K ψ hχ b]
    by_cases hb : IsCoprime b.val m <;> by_cases hbm : IsCoprime b.val M <;>
      simp [hb, hbm]
  · rw [ite_eq_right ha]
    have hz (b : J₀) : f (e.symm (a,b)) = 0 := by
      unfold f
      rw [hnorm, hJ, pow_two, IsCoprime.mul_left_iff, IsCoprime.mul_left_iff, and_self]
      exact ite_eq_right (fun h => ha ⟨h.1.1, h.2⟩)
    simp_rw [hz, tsum_zero]

end
end ArtinMatthews
