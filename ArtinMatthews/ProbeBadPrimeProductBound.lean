module

public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusBound


set_option backward.privateInPublic true
@[expose] public section

/-! A finite product on the actual prime support of an ideal loses only
an arbitrarily small power of that ideal's norm. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem exists_probe_primeSupport_product_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Ideal (𝓞 K)), I ≠ ⊥ →
      ∀ (F : (HeckeIdealMobius.primeSupport K I) → ℂ),
      (∀ P, ‖F P‖ ≤ 64) →
      ‖∏ P, F P‖ ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  obtain ⟨B, hB, hbound⟩ := HeckeIdealMobius.prime_support_subsets_bound K (ε / 6) (by positivity)
  refine ⟨B ^ 6, by positivity, fun I hI F hF => ?_⟩
  have hN : 0 ≤ (Ideal.absNorm I : ℝ) := Nat.cast_nonneg _
  have h6 := pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℝ) ^ (HeckeIdealMobius.primeSupport K I).card)
    (hbound I hI) 6
  have hpow : ((Ideal.absNorm I : ℝ) ^ (ε / 6)) ^ 6 = (Ideal.absNorm I : ℝ) ^ ε := by
    rw [← Real.rpow_mul_natCast hN]
    congr 1
    ring
  have h64 : ((2 : ℝ) ^ (HeckeIdealMobius.primeSupport K I).card) ^ 6 =
      (64 : ℝ) ^ (HeckeIdealMobius.primeSupport K I).card := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [mul_pow, hpow, h64] at h6
  apply le_trans ?_ h6
  rw [norm_prod]
  calc
    _ ≤ ∏ _P : (HeckeIdealMobius.primeSupport K I), (64 : ℝ) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun P _ => hF P)
    _ = _ := by simp

theorem exists_probe_primeSubset_product_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Ideal (𝓞 K)), I ≠ ⊥ →
      ∀ (T : Finset (Ideal (𝓞 K))), T ⊆ HeckeIdealMobius.primeSupport K I →
      ∀ (F : T → ℂ), (∀ P, ‖F P‖ ≤ 64) →
      ‖∏ P, F P‖ ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  obtain ⟨C, hC, h⟩ := exists_probe_primeSupport_product_bound K ε hε
  refine ⟨C, hC, fun I hI T hT F hF => ?_⟩
  have hc : (64 : ℝ) ^ (HeckeIdealMobius.primeSupport K I).card ≤
      C * (Ideal.absNorm I : ℝ) ^ ε := by
    simpa using h I hI (fun _ => (64 : ℂ)) (by norm_num)
  calc
    _ ≤ ∏ _P : T, (64 : ℝ) := by
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun P _ => hF P)
    _ = (64 : ℝ) ^ T.card := by simp
    _ ≤ (64 : ℝ) ^ (HeckeIdealMobius.primeSupport K I).card :=
      pow_le_pow_right₀ (by norm_num) (Finset.card_le_card hT)
    _ ≤ _ := hc

end
end ArtinMatthews.VaryingKummerAnalytic
