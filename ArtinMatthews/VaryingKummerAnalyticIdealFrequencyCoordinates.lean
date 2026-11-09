module

public import ArtinMatthews.VaryingKummerAnalyticIdealFrequencyLabelSeparation


set_option backward.privateInPublic true
@[expose] public section

/-! Trace frequencies in a genuine common integral basis of the ring of
integers. Integer translations are lifted by the actual trace-dual basis. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module FractionalIdeal
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

abbrev IdealFrequencyCoordinateIndex := Free.ChooseBasisIndex ℤ (𝓞 K)

theorem idealFrequencyCoordinateIndex_card :
    Fintype.card (IdealFrequencyCoordinateIndex K) = Module.finrank ℚ K :=
  (Module.finrank_eq_card_basis (NumberField.integralBasis K)).symm

/-- The actual integer coordinates in the common ring-of-integers basis. -/
def idealIntegerCoordinates (a : 𝓞 K) : IdealFrequencyCoordinateIndex K → ℤ :=
  (NumberField.RingOfIntegers.basis K).repr a

/-- Literal real trace frequencies, including the full complex-place trace. -/
def idealTraceCoordinates (α : K) : IdealFrequencyCoordinateIndex K → ℝ :=
  fun j => (Algebra.trace ℚ K (α * NumberField.integralBasis K j) : ℝ)

theorem idealIntegerCoordinates_expansion (a : 𝓞 K) :
    (a : K) = ∑ j, (idealIntegerCoordinates K a j : ℚ) •
      NumberField.integralBasis K j := by
  simpa [idealIntegerCoordinates] using
    ((NumberField.integralBasis K).sum_repr (a : K)).symm

theorem idealTrace_pairing_eq_sum_rat (a : 𝓞 K) (α : K) :
    Algebra.trace ℚ K (α * (a : K)) =
      ∑ j, (idealIntegerCoordinates K a j : ℚ) *
        Algebra.trace ℚ K (α * NumberField.integralBasis K j) := by
  rw [idealIntegerCoordinates_expansion K a]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]

/-- The actual trace phase is the ordinary integer-coordinate dot product. -/
theorem idealTrace_pairing_eq_sum (a : 𝓞 K) (α : K) :
    (Algebra.trace ℚ K (α * (a : K)) : ℝ) =
      ∑ j, (idealIntegerCoordinates K a j : ℝ) * idealTraceCoordinates K α j := by
  rw [idealTrace_pairing_eq_sum_rat]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, idealTraceCoordinates]

theorem idealTraceCoordinates_add (α β : K) :
    idealTraceCoordinates K (α + β) = idealTraceCoordinates K α + idealTraceCoordinates K β := by
  ext j
  simp only [idealTraceCoordinates, add_mul, map_add, Rat.cast_add, Pi.add_apply]

theorem idealTraceCoordinates_sub (α β : K) :
    idealTraceCoordinates K (α - β) = idealTraceCoordinates K α - idealTraceCoordinates K β := by
  ext j
  simp only [idealTraceCoordinates, sub_mul, map_sub, Rat.cast_sub, Pi.sub_apply]

/-- The inverse trace-coordinate map on the integer lattice. -/
def idealTraceIntegerLift (k : IdealFrequencyCoordinateIndex K → ℤ) : K :=
  ∑ j, k j • (NumberField.integralBasis K).traceDual j

theorem idealTraceIntegerLift_coordinates (k : IdealFrequencyCoordinateIndex K → ℤ) :
    idealTraceCoordinates K (idealTraceIntegerLift K k) = fun j => (k j : ℝ) := by
  ext j
  simp only [idealTraceCoordinates, idealTraceIntegerLift, Finset.sum_mul,
    smul_mul_assoc, map_sum, map_zsmul, Basis.trace_traceDual_mul]
  simp

/-- Integral trace coordinates characterize exactly the actual trace-dual
fractional ideal of the ring of integers. -/
theorem idealTraceCoordinates_integral_iff (α : K) :
    (∃ k : IdealFrequencyCoordinateIndex K → ℤ,
      idealTraceCoordinates K α = fun j => (k j : ℝ)) ↔
      α ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.mem_dual one_ne_zero]
  constructor
  · rintro ⟨k, hk⟩ y hy
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mp hy
    have hq (j : IdealFrequencyCoordinateIndex K) :
        Algebra.trace ℚ K (α * NumberField.integralBasis K j) = (k j : ℚ) := by
      have hj := congrFun hk j
      change (Algebra.trace ℚ K (α * NumberField.integralBasis K j) : ℝ) = (k j : ℝ) at hj
      exact_mod_cast hj
    refine ⟨∑ j, idealIntegerCoordinates K a j * k j, ?_⟩
    change ((∑ j, idealIntegerCoordinates K a j * k j : ℤ) : ℚ) =
      Algebra.trace ℚ K (α * (a : K))
    rw [idealTrace_pairing_eq_sum_rat]
    simp only [hq, Int.cast_sum, Int.cast_mul]
  · intro h
    have hi (j : IdealFrequencyCoordinateIndex K) :
        ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ K (α * NumberField.integralBasis K j) := by
      apply h
      rw [integralBasis_apply]
      exact FractionalIdeal.coe_mem_one (𝓞 K)⁰ _
    choose k hk using hi
    refine ⟨k, funext fun j => ?_⟩
    change (Algebra.trace ℚ K (α * NumberField.integralBasis K j) : ℝ) = (k j : ℝ)
    exact_mod_cast (hk j).symm

theorem idealTraceIntegerLift_mem_dual (k : IdealFrequencyCoordinateIndex K → ℤ) :
    idealTraceIntegerLift K k ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) :=
  (idealTraceCoordinates_integral_iff K _).mp ⟨k, idealTraceIntegerLift_coordinates K k⟩

/-- A field-only bound for reconstruction from trace coordinates. -/
def idealTraceReconstructionConstant : ℝ :=
  1 + ∑ j, ‖mixedEmbedding K ((NumberField.integralBasis K).traceDual j)‖

theorem idealTraceReconstructionConstant_pos : 0 < idealTraceReconstructionConstant K := by
  unfold idealTraceReconstructionConstant
  positivity

theorem mixedEmbedding_eq_trace_coordinate_sum (α : K) :
    mixedEmbedding K α = ∑ j, idealTraceCoordinates K α j •
      mixedEmbedding K ((NumberField.integralBasis K).traceDual j) := by
  conv_lhs => rw [← ((NumberField.integralBasis K).traceDual).sum_repr α]
  simp only [map_sum, map_rat_smul, Basis.traceDual_repr_apply,
    Algebra.traceForm_apply, idealTraceCoordinates]
  apply Finset.sum_congr rfl
  intro j _
  exact ratCast_smul_eq ℚ ℝ _ _

theorem mixedEmbedding_norm_le_trace_coordinates (α : K) :
    ‖mixedEmbedding K α‖ ≤ idealTraceReconstructionConstant K * ‖idealTraceCoordinates K α‖ := by
  rw [mixedEmbedding_eq_trace_coordinate_sum K α]
  calc
    ‖∑ j, idealTraceCoordinates K α j •
        mixedEmbedding K ((NumberField.integralBasis K).traceDual j)‖ ≤
      ∑ j, ‖idealTraceCoordinates K α j •
        mixedEmbedding K ((NumberField.integralBasis K).traceDual j)‖ := norm_sum_le _ _
    _ = ∑ j, ‖idealTraceCoordinates K α j‖ *
        ‖mixedEmbedding K ((NumberField.integralBasis K).traceDual j)‖ := by
      simp only [norm_smul]
    _ ≤ ∑ j, ‖idealTraceCoordinates K α‖ *
        ‖mixedEmbedding K ((NumberField.integralBasis K).traceDual j)‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm (idealTraceCoordinates K α) j)
        (norm_nonneg _)
    _ ≤ idealTraceReconstructionConstant K * ‖idealTraceCoordinates K α‖ := by
      rw [← Finset.mul_sum]
      simp only [idealTraceReconstructionConstant, add_mul, one_mul]
      nlinarith [norm_nonneg (idealTraceCoordinates K α)]

/-- The common integral coordinates are controlled by the mixed embedding. -/
def idealIntegerCoordinateConstant : ℝ :=
  1 + ‖(mixedEmbedding.latticeBasis K).equivFunL.toContinuousLinearMap‖

theorem idealIntegerCoordinateConstant_pos : 0 < idealIntegerCoordinateConstant K := by
  unfold idealIntegerCoordinateConstant
  positivity

theorem idealIntegerCoordinates_real_eq (a : 𝓞 K) :
    (fun j => (idealIntegerCoordinates K a j : ℝ)) =
      (mixedEmbedding.latticeBasis K).equivFunL (mixedEmbedding K (a : K)) := by
  ext j
  change (idealIntegerCoordinates K a j : ℝ) =
    (mixedEmbedding.latticeBasis K).repr (mixedEmbedding K (a : K)) j
  rw [mixedEmbedding.latticeBasis_repr_apply, integralBasis_repr_apply]
  rfl

theorem idealIntegerCoordinates_norm_le (a : 𝓞 K) :
    ‖fun j => (idealIntegerCoordinates K a j : ℝ)‖ ≤
      idealIntegerCoordinateConstant K * ‖mixedEmbedding K (a : K)‖ := by
  rw [idealIntegerCoordinates_real_eq]
  have h := (mixedEmbedding.latticeBasis K).equivFunL.toContinuousLinearMap.le_opNorm
    (mixedEmbedding K (a : K))
  apply h.trans
  simp only [idealIntegerCoordinateConstant, add_mul, one_mul]
  nlinarith [norm_nonneg (mixedEmbedding K (a : K))]

end
end ArtinMatthews.VaryingKummerAnalytic
