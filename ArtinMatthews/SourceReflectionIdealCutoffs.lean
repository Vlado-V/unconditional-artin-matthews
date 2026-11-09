module

public import ArtinMatthews.SourceReflectionExteriorRows
public import ArtinMatthews.SourceReflectionDyadicIndex
public import Mathlib.Data.Finset.Preimage


set_option backward.privateInPublic true
@[expose] public section

/-! Finite exterior norm cutoffs and the ideal harmonic bound from the
fixed-field linear ideal count. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

def sourceReflectionBoundedExponents (X : ℝ) : Finset E :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊X⌋₊).toFinset.preimage
    (sourcePrimeExponentIdeal F S₀) (sourcePrimeExponentIdeal_injective F S₀).injOn

@[simp] theorem sourceReflection_mem_boundedExponents {X : ℝ} (hX : 0 ≤ X) (e : E) :
    e ∈ sourceReflectionBoundedExponents F S₀ X ↔ (q e : ℝ) ≤ X := by
  rw [sourceReflectionBoundedExponents, Finset.mem_preimage, Set.Finite.mem_toFinset]
  change (sourcePrimeExponentIdeal F S₀ e).absNorm ≤ ⌊X⌋₊ ↔ _
  rw [sourcePrimeExponentIdeal_norm, Nat.le_floor_iff hX]

theorem sourceReflection_norm_one_le (e : E) : (1 : ℝ) ≤ q e := by
  exact_mod_cast sourcePrimeExponentNorm_pos F S₀ e

theorem exists_sourceReflectionDyadReciprocal_le :
    ∃ B : ℝ, 0 < B ∧ ∀ C : ℝ, 1 ≤ C → ∀ A : Finset E,
      (∀ e ∈ A, C ≤ (q e : ℝ) ∧ (q e : ℝ) ≤ 2 * C) →
      ∑ e ∈ A, (q e : ℝ)⁻¹ ≤ B := by
  obtain ⟨B, hB, hb⟩ := exists_sourceReflectionExteriorCard_le F S₀
  refine ⟨2 * B, by positivity, fun C hC A hA => ?_⟩
  have hc := zero_lt_one.trans_le hC
  have hcard := hb (2 * C) (by linarith) A (fun e he => (hA e he).2)
  calc
    _ ≤ ∑ _e ∈ A, C⁻¹ :=
      Finset.sum_le_sum (fun e he => (inv_le_inv₀ (hc.trans_le (hA e he).1) hc).mpr (hA e he).1)
    _ = (A.card : ℝ) * C⁻¹ := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (B * (2 * C)) * C⁻¹ := mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hc.le)
    _ = 2 * B := by field_simp

theorem exists_sourceReflectionHarmonic_le :
    ∃ B : ℝ, 0 < B ∧ ∀ X : ℝ, 1 ≤ X → ∀ A : Finset E,
      (∀ e ∈ A, (q e : ℝ) ≤ X) →
      ∑ e ∈ A, (q e : ℝ)⁻¹ ≤ B * Real.log (2 * X) := by
  obtain ⟨B, hB, hb⟩ := exists_sourceReflectionDyadReciprocal_le F S₀
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨B / Real.log 2, div_pos hB hlog, fun X hX A hA => ?_⟩
  let T := Finset.range (sourceReflectionDyadLength X)
  let b (e : E) := Nat.log 2 (q e)
  have hsub (e : E) (he : e ∈ A) : b e ∈ T :=
    Finset.mem_range.mpr (sourceReflectionDyad_lt_length (hA e he))
  have hdyad (j : ℕ) :
      ∑ e ∈ A.filter (fun e => b e = j), (q e : ℝ)⁻¹ ≤ B := by
    apply hb ((2 : ℝ) ^ j) (one_le_pow₀ (by norm_num))
    intro e he
    have hj := (Finset.mem_filter.mp he).2
    have h := sourceReflectionDyad_bounds (sourcePrimeExponentNorm_pos F S₀ e)
    change Nat.log 2 (q e) = j at hj
    rw [hj] at h
    exact ⟨h.1, h.2.le⟩
  calc
    _ = ∑ j ∈ T, ∑ e ∈ A.filter (fun e => b e = j), (q e : ℝ)⁻¹ :=
      (Finset.sum_fiberwise_of_maps_to hsub _).symm
    _ ≤ ∑ _j ∈ T, B := Finset.sum_le_sum (fun j _ => hdyad j)
    _ = (sourceReflectionDyadLength X : ℝ) * B := by
      simp only [Finset.sum_const, nsmul_eq_mul, T, Finset.card_range]
    _ ≤ (Real.log (2 * X) / Real.log 2) * B :=
      mul_le_mul_of_nonneg_right (sourceReflectionDyadLength_le_log hX) hB.le
    _ = _ := by ring

end
end ArtinMatthews.SourceEulerAssembly
