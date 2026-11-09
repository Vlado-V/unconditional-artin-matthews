module

public import ArtinMatthews.SourceReflectionRetainedNorm
public import ArtinMatthews.SourceReflectionTail


set_option backward.privateInPublic true
@[expose] public section

/-! The retained and tail square masses on a powerful/simple dyad.
Each powerful part is squared separately. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {U : Type} [Fintype U] (A : SourceReflectionExpansionData F S₀ U)

local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

theorem sourceReflectionRpow_sq {x : ℝ} (hx : 0 ≤ x) (r : ℝ) :
    (x ^ r) ^ 2 = x ^ (2 * r) := by
  rw [← Real.rpow_natCast (x ^ r) 2, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

theorem exists_sourceReflectionRetainedDyadMass_le
    (hsieve : SourceReflectionQuadraticSieve F S₀ hζ) {δ₁ δ₂ : ℝ}
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z R P D : ℝ, 0 < Z → 1 ≤ R → 1 ≤ P → 1 ≤ D →
      ∀ (H : Finset E) (rows : E → Finset E),
        (∀ h ∈ H, sourceReflectionIsPowerful h ∧ (q h : ℝ) ≤ 2 * P) →
        (∀ h ∈ H, ∀ d ∈ rows h, sourceReflectionIsSquarefree d ∧ D ≤ (q d : ℝ) ∧ (q d : ℝ) < 2 * D) →
        ∑ h ∈ H, ∑ d ∈ rows h,
          ‖sourceReflectionSelectedRow F S₀ hζ A Z h d (fun Q => Q ≤ R)‖ ^ 2 ≤
          C * (Real.sqrt P * P ^ (2 * δ₁) * (Real.log (2 * R)) ^ 4 * (D + R) * (D * R) ^ δ₂) := by
  obtain ⟨B, hB, hb⟩ := exists_sourceReflectionRetainedRow_norm_le F S₀ hζ A hsieve hδ₁ hδ₂
  obtain ⟨C, hC, hc⟩ := exists_sourceReflectionExteriorPowerfulCard_le F S₀
  refine ⟨C * Real.sqrt 2 * B ^ 2, by positivity, ?_⟩
  intro Z R P D hZ hR hP hD H rows hH hrows
  have hP₀ := zero_le_one.trans hP
  have hD₀ := zero_le_one.trans hD
  have hR₀ := zero_le_one.trans hR
  let V := P ^ (2 * δ₁) * (Real.log (2 * R)) ^ 4 * (D + R) * (D * R) ^ δ₂
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hH' : (H.card : ℝ) ≤ C * Real.sqrt 2 * Real.sqrt P := by
    rw [mul_assoc, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact hc (2 * P) (by linarith) H hH
  have hmass (h : E) (hh : h ∈ H) :
      ∑ d ∈ rows h, ‖sourceReflectionSelectedRow F S₀ hζ A Z h d (fun Q => Q ≤ R)‖ ^ 2 ≤
        B ^ 2 * V := by
    rw [← sourceReflectionRowVector_norm_sq]
    have h := hb Z R P D hZ hR hP hD (rows h) (hrows h hh) h (hH h hh).2
    refine (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq ?_
    dsimp [V]
    simp only [mul_pow, sourceReflectionRpow_sq hP₀, sourceReflectionRpow_sq (mul_nonneg hD₀ hR₀),
      Real.sq_sqrt (add_nonneg hD₀ hR₀), show 2 * (δ₂ / 2) = δ₂ by ring, ← pow_mul]
    ring
  calc
    _ ≤ ∑ _h ∈ H, B ^ 2 * V := Finset.sum_le_sum hmass
    _ = (H.card : ℝ) * (B ^ 2 * V) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C * Real.sqrt 2 * Real.sqrt P) * (B ^ 2 * V) :=
      mul_le_mul_of_nonneg_right hH' (by positivity)
    _ = _ := by dsimp [V]; ring

theorem exists_sourceReflectionTailDyadMass_le {δ δ₁ N σ : ℝ}
    (hδ₁ : 0 < δ₁) (hσ : 1 / 2 < σ) (hN : σ ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z P D : ℝ, 0 < Z → 1 ≤ P → 1 ≤ D →
      ∀ (H : Finset E) (rows : E → Finset E),
        (∀ h ∈ H, sourceReflectionIsPowerful h ∧ (q h : ℝ) ≤ 2 * P) →
        (∀ h ∈ H, ∀ d ∈ rows h, (q d : ℝ) ≤ 2 * D) →
        ∑ h ∈ H, ∑ d ∈ rows h,
          ‖sourceReflectionSelectedRow F S₀ hζ A Z h d (fun Q => sourceReflectionCutoff Z P D δ < Q)‖ ^ 2 ≤
          C * (Real.sqrt P * P ^ (2 * δ₁) * D * sourceReflectionLength Z P D ^ (2 * σ) *
            sourceReflectionTailScale Z P D δ ^ (-2 * (N - σ))) := by
  obtain ⟨B, hB, hb⟩ := exists_sourceReflectionTailRow_le F S₀ hζ A (δ := δ) hδ₁ hσ hN
  obtain ⟨C, hC, hc⟩ := exists_sourceReflectionExteriorPowerfulCard_le F S₀
  obtain ⟨G, hG, hg⟩ := exists_sourceReflectionExteriorCard_le F S₀
  refine ⟨C * Real.sqrt 2 * (2 * G) * B ^ 2, by positivity, ?_⟩
  intro Z P D hZ hP hD H rows hH hrows
  let L := sourceReflectionLength Z P D
  let J := sourceReflectionTailScale Z P D δ
  have hP₀ := zero_le_one.trans hP
  have hL : 0 ≤ L := (sourceReflectionLength_pos hZ (zero_lt_one.trans_le hP) (zero_lt_one.trans_le hD)).le
  have hJ : 0 ≤ J := (Real.rpow_nonneg hZ.le δ).trans (le_max_left _ _)
  let V := B ^ 2 * P ^ (2 * δ₁) * L ^ (2 * σ) * J ^ (-2 * (N - σ))
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hH' : (H.card : ℝ) ≤ C * Real.sqrt 2 * Real.sqrt P := by
    rw [mul_assoc, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact hc (2 * P) (by linarith) H hH
  have hmass (h : E) (hh : h ∈ H) :
      ∑ d ∈ rows h, ‖sourceReflectionSelectedRow F S₀ hζ A Z h d
        (fun Q => sourceReflectionCutoff Z P D δ < Q)‖ ^ 2 ≤ G * (2 * D) * V := by
    have hn := hg (2 * D) (by linarith) (rows h) (hrows h hh)
    calc
      _ ≤ ∑ _d ∈ rows h, V := by
        apply Finset.sum_le_sum
        intro d hd
        have h := hb Z P D hZ hP hD h d (hH h hh).1 (hH h hh).2 (hrows h hh d hd)
        refine (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq ?_
        change (B * P ^ δ₁ * L ^ σ * J ^ (-(N - σ))) ^ 2 = V
        dsimp [V]
        simp only [mul_pow, sourceReflectionRpow_sq hP₀, sourceReflectionRpow_sq hL,
          sourceReflectionRpow_sq hJ, mul_neg, neg_mul]
      _ = ((rows h).card : ℝ) * V := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hn hV
  calc
    _ ≤ ∑ _h ∈ H, G * (2 * D) * V := Finset.sum_le_sum hmass
    _ = (H.card : ℝ) * (G * (2 * D) * V) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C * Real.sqrt 2 * Real.sqrt P) * (G * (2 * D) * V) :=
      mul_le_mul_of_nonneg_right hH' (by positivity)
    _ = _ := by dsimp [V]; ring

end
end ArtinMatthews.SourceEulerAssembly
