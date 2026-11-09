module

public import ArtinMatthews.SourceQuadraticSmallEuler
public import ArtinMatthews.SourceQuadraticSmallRowBall


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀

def sourceQuadraticSmallEulerCoeff (u : E → ℂ) (s : ℂ) (b : E) : ℂ :=
  u b * quadraticSmallEuler F (I b) s

theorem sourceQuadraticSmallEulerCoeff_mass (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N → ∀ cols : Finset E,
      (∀ b ∈ cols, (q b : ℝ) ≤ N) → ∀ (u : E → ℂ) (s : ℂ), 0 ≤ s.re →
      sourceQuadraticSmallWeightedMass F S₀ cols (sourceQuadraticSmallEulerCoeff F S₀ u s) ≤
        C * N ^ η * coeffMass cols u := by
  obtain ⟨Ce, hCe, he⟩ := quadraticSmallEuler_subpower F (η / 4) (by positivity)
  obtain ⟨Ct, hCt, ht⟩ := sourceQuadraticSquarefreeDivisors_small_power F S₀ (η / 2) (by positivity)
  refine ⟨Ct * Ce ^ 2, by positivity, ?_⟩
  intro N hN cols hcols u s hs
  have hN0 := zero_lt_one.trans_le hN
  have hpow : N ^ (η / 2) * (N ^ (η / 4)) ^ 2 = N ^ η := by
    rw [pow_two, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
    congr 1
    ring
  have htw (b : E) (hb : b ∈ cols) : (2 : ℝ) ^ b.support.card ≤ Ct * N ^ (η / 2) := by
    have h := ht b
    rw [sourceQuadraticSquarefreeDivisors_card, Nat.cast_pow, Nat.cast_ofNat] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hcols b hb) (by positivity)) hCt.le)
  have hel (b : E) (hb : b ∈ cols) : ‖quadraticSmallEuler F (I b) s‖ ≤ Ce * N ^ (η / 4) := by
    have h := he (I b) (sourcePrimeExponentIdeal_ne_bot F S₀ b) s hs
    rw [sourcePrimeExponentIdeal_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hcols b hb) (by positivity)) hCe.le)
  unfold sourceQuadraticSmallWeightedMass coeffMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  rw [sourceQuadraticSmallEulerCoeff, norm_mul, mul_pow]
  calc
    _ ≤ (Ct * N ^ (η / 2)) * (‖u b‖ ^ 2 * (Ce * N ^ (η / 4)) ^ 2) := by
      gcongr
      · exact htw b hb
      · exact hel b hb
    _ = (Ct * Ce ^ 2) * (N ^ (η / 2) * (N ^ (η / 4)) ^ 2) * ‖u b‖ ^ 2 := by ring
    _ = _ := by rw [hpow]

theorem sourceQuadraticSmallEulerCoeff_star_mass (cols : Finset E) (u : E → ℂ) (s : ℂ) :
    sourceQuadraticSmallWeightedMass F S₀ cols (fun b => u b * star (quadraticSmallEuler F (I b) s)) =
      sourceQuadraticSmallWeightedMass F S₀ cols (sourceQuadraticSmallEulerCoeff F S₀ u s) := by
  simp only [sourceQuadraticSmallWeightedMass, sourceQuadraticSmallEulerCoeff, norm_mul, norm_star]

end
end ArtinMatthews.SourceEulerAssembly
