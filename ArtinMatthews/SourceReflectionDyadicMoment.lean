module

public import ArtinMatthews.SourceReflectionBranchMass


set_option backward.privateInPublic true
@[expose] public section

/-! The Section 04 dyadic moment from the exact reflected series and
the exterior quadratic sieve. -/
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

theorem sourceReflection_norm_add_sq_le (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2).trans ?_
  nlinarith only [sq_nonneg (‖a‖ - ‖b‖)]

theorem exists_sourceReflectionDyadicMoment_le
    (hsieve : SourceReflectionQuadraticSieve F S₀ hζ) {K M ε : ℝ}
    (hK : 1 ≤ K) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z P D : ℝ, 1 ≤ Z → 1 ≤ P → 1 ≤ D → P * D ≤ K * Z ^ M →
      ∀ (H : Finset E) (rows : E → Finset E),
        (∀ h ∈ H, sourceReflectionIsPowerful h ∧ (q h : ℝ) ≤ 2 * P) →
        (∀ h ∈ H, ∀ d ∈ rows h, sourceReflectionIsSquarefree d ∧ D ≤ (q d : ℝ) ∧ (q d : ℝ) < 2 * D) →
        ∑ h ∈ H, ∑ d ∈ rows h, ‖sourceReflectionSelectedRow F S₀ hζ A Z h d (fun _ => True)‖ ^ 2 ≤
          C * Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z) := by
  obtain ⟨δ, δ₁, δ₂, δ₃, hδ, hδ₁, hδ₂, hδ₃, hbudget⟩ := sourceReflectionLossParameters hM hε
  obtain ⟨N, hN, hN'⟩ := sourceReflectionTailOrder (σ := 1) (A := 1)
    hM hδ hδ₁.le zero_le_one zero_le_one
  obtain ⟨C₁, hC₁, h₁⟩ := exists_sourceReflectionRetainedDyadMass_le F S₀ hζ A hsieve hδ₁ hδ₂
  obtain ⟨C₂, hC₂, h₂⟩ := exists_sourceReflectionTailDyadMass_le F S₀ hζ A (δ := δ) hδ₁
    (by norm_num : (1 / 2 : ℝ) < 1) hN.le
  obtain ⟨C₃, hC₃, h₃⟩ := sourceReflectionRetainedBudget hK hM hδ.le hδ₁.le hδ₂.le hδ₃ hbudget
  let T := C₂ * (K ^ (2 * δ₁) * (8 * K ^ 2) ^ ((2 : ℝ) * 1))
  let B := C₁ * C₃
  have hT : 0 < T := by dsimp [T]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨2 * (B + T), by positivity, ?_⟩
  intro Z P D hZ hP hD hPD H rows hH hrows
  have hz := zero_lt_one.trans_le hZ
  have hp := zero_le_one.trans hP
  have hd := zero_le_one.trans hD
  let R := sourceReflectionCutoff Z P D δ
  let ret (h d : E) := sourceReflectionSelectedRow F S₀ hζ A Z h d (fun Q => Q ≤ R)
  let tail (h d : E) := sourceReflectionSelectedRow F S₀ hζ A Z h d (fun Q => R < Q)
  let V := D + D ^ 2 * P / Z
  have hV : D ≤ V := by
    dsimp [V]
    exact le_add_of_nonneg_right (by positivity)
  have hret : ∑ h ∈ H, ∑ d ∈ rows h, ‖ret h d‖ ^ 2 ≤ B * Z ^ ε * Real.sqrt P * V := by
    by_cases hR : 1 ≤ R
    · have hm := h₁ Z R P D hz hR hP hD H rows hH hrows
      have hb := h₃ Z P D hZ hP hD hPD hR
      exact hm.trans ((mul_le_mul_of_nonneg_left hb hC₁.le).trans_eq (by dsimp [B, V]; ring))
    · have hr : R < 1 := lt_of_not_ge hR
      have he (h d : E) : ret h d = 0 := by
        unfold ret sourceReflectionSelectedRow
        simp only [sourceReflectionRetainedBranch_zero_of_lt_one F S₀ hζ A Z h d _ _ hr, Finset.sum_const_zero]
      simp only [he, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero]
      exact mul_nonneg (by positivity) (hd.trans hV)
  have ht : ∑ h ∈ H, ∑ d ∈ rows h, ‖tail h d‖ ^ 2 ≤ T * Z ^ ε * Real.sqrt P * V := by
    have hm := h₂ Z P D hz hP hD H rows hH (fun h hh d hdd => (hrows h hh d hdd).2.2.le)
    have hb := sourceReflectionTailBudget hZ hK hP hD hPD hδ₁.le zero_le_one hN.le hN'.le
    calc
      _ ≤ T * Real.sqrt P * D * Z ^ (-1 : ℝ) :=
        hm.trans ((mul_le_mul_of_nonneg_left hb hC₂.le).trans_eq (by dsimp [T]; ring))
      _ ≤ T * Real.sqrt P * D * Z ^ ε :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
      _ = T * Z ^ ε * Real.sqrt P * D := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hV (by positivity)
  calc
    _ ≤ ∑ h ∈ H, ∑ d ∈ rows h, 2 * (‖ret h d‖ ^ 2 + ‖tail h d‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro h _
      apply Finset.sum_le_sum
      intro d _
      rw [sourceReflectionSelectedRow_split F S₀ hζ A hz h d R]
      exact sourceReflection_norm_add_sq_le _ _
    _ = 2 * ((∑ h ∈ H, ∑ d ∈ rows h, ‖ret h d‖ ^ 2) +
        (∑ h ∈ H, ∑ d ∈ rows h, ‖tail h d‖ ^ 2)) := by
      simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    _ ≤ 2 * (B * Z ^ ε * Real.sqrt P * V + T * Z ^ ε * Real.sqrt P * V) :=
      mul_le_mul_of_nonneg_left (add_le_add hret ht) (by norm_num)
    _ = _ := by dsimp [V]; ring

end
end ArtinMatthews.SourceEulerAssembly
