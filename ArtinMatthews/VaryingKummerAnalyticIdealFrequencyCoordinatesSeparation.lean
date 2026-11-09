module

public import ArtinMatthews.VaryingKummerAnalyticIdealFrequencyCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! Actual coordinate spacing for ideal/residue frequencies, uniformly under
every integer translation in the common integral basis. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def idealFrequencyLabelCoordinates (ℓ : IdealFrequencyLabel K) :
    IdealFrequencyCoordinateIndex K → ℝ :=
  idealTraceCoordinates K (idealFrequencyLabelValue K ℓ)

theorem idealFrequencyLabel_coordinates_injective_mod_integers
    {ℓ ℓ' : IdealFrequencyLabel K} (k : IdealFrequencyCoordinateIndex K → ℤ)
    (h : idealFrequencyLabelCoordinates K ℓ - idealFrequencyLabelCoordinates K ℓ' =
      fun j => (k j : ℝ)) : ℓ = ℓ' := by
  apply idealFrequencyLabel_eq_of_sub_mem_dual K
  apply (idealTraceCoordinates_integral_iff K _).mp
  refine ⟨k, ?_⟩
  rw [idealTraceCoordinates_sub]
  exact h

theorem idealFrequencyLabel_coordinates_power_separation
    {ℓ ℓ' : IdealFrequencyLabel K} (hne : ℓ ≠ ℓ')
    (k : IdealFrequencyCoordinateIndex K → ℤ) {U : ℝ}
    (hℓU : (Ideal.absNorm ℓ.1.val : ℝ) ≤ U)
    (hℓ'U : (Ideal.absNorm ℓ'.1.val : ℝ) ≤ U) :
    1 / (|(NumberField.discr K : ℝ)| * U ^ 2) ≤
      (idealTraceReconstructionConstant K *
        ‖idealFrequencyLabelCoordinates K ℓ - idealFrequencyLabelCoordinates K ℓ' +
          fun j => (k j : ℝ)‖) ^ Module.finrank ℚ K := by
  have hs := idealFrequencyLabel_mixed_separation_norm_cutoff K hne
    (idealTraceIntegerLift_mem_dual K k) hℓU hℓ'U
  have hb := mixedEmbedding_norm_le_trace_coordinates K
    (idealFrequencyLabelValue K ℓ - idealFrequencyLabelValue K ℓ' + idealTraceIntegerLift K k)
  rw [idealTraceCoordinates_add, idealTraceCoordinates_sub,
    idealTraceIntegerLift_coordinates] at hb
  exact hs.trans (pow_le_pow_left₀ (norm_nonneg _) hb _)

/-- A positive spacing radius retaining its exact discriminant and cutoff
dependence. The coordinate reconstruction loss depends on the field alone. -/
def idealCoordinateSeparationRadius (U : ℝ) : ℝ :=
  (1 / (|(NumberField.discr K : ℝ)| * U ^ 2)) ^
      (Module.finrank ℚ K : ℝ)⁻¹ / idealTraceReconstructionConstant K

theorem idealCoordinateSeparationRadius_pos {U : ℝ} (hU : 0 < U) :
    0 < idealCoordinateSeparationRadius K U := by
  have hD : 0 < |(NumberField.discr K : ℝ)| := abs_pos.mpr (by
    exact_mod_cast NumberField.discr_ne_zero K)
  exact div_pos (Real.rpow_pos_of_pos (one_div_pos.mpr (mul_pos hD (sq_pos_of_pos hU))) _)
    (idealTraceReconstructionConstant_pos K)

theorem idealFrequencyLabel_coordinates_separation
    {ℓ ℓ' : IdealFrequencyLabel K} (hne : ℓ ≠ ℓ')
    (k : IdealFrequencyCoordinateIndex K → ℤ) {U : ℝ}
    (hℓU : (Ideal.absNorm ℓ.1.val : ℝ) ≤ U)
    (hℓ'U : (Ideal.absNorm ℓ'.1.val : ℝ) ≤ U) :
    idealCoordinateSeparationRadius K U ≤
      ‖idealFrequencyLabelCoordinates K ℓ - idealFrequencyLabelCoordinates K ℓ' +
        fun j => (k j : ℝ)‖ := by
  have hpow := idealFrequencyLabel_coordinates_power_separation K hne k hℓU hℓ'U
  have hn : Module.finrank ℚ K ≠ 0 := (Module.finrank_pos : 0 < Module.finrank ℚ K).ne'
  have hroot := Real.rpow_le_rpow (by positivity :
      0 ≤ 1 / (|(NumberField.discr K : ℝ)| * U ^ 2)) hpow
    (inv_nonneg.mpr (Nat.cast_nonneg (Module.finrank ℚ K)))
  rw [Real.pow_rpow_inv_natCast
    (mul_nonneg (idealTraceReconstructionConstant_pos K).le (norm_nonneg _)) hn] at hroot
  exact (div_le_iff₀ (idealTraceReconstructionConstant_pos K)).mpr
    (by simpa only [mul_comm] using hroot)

end
end ArtinMatthews.VaryingKummerAnalytic
