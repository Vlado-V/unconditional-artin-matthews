module

public import ArtinMatthews.MarkedSparsePhaseKernel
public import OAI.NumberTheory.JointDickman.Analysis.LogPhaseSharpBounds
public import OAI.NumberTheory.JointDickman.Analysis.LogPhaseUniform


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform integer logarithmic-phase cancellation, obtained from the
existing first/second derivative and bounded-order differencing proofs in
OpenAI math-main. These are bounds for the actual finite sum. -/

namespace ArtinMatthews

open Filter OAI.JointDickman OAI.Problem337
open scoped Topology BigOperators

noncomputable section

theorem marked_log_phase_reciprocal_power (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1/2 ∧
      ∀ᶠ U : ℝ in atTop, ∀ (Z : ℝ) (L R : ℕ),
        |Z| ≤ U^B → U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        ‖∑ n ∈ Finset.Icc L R, ExponentialSum.phase (Z*Real.log (n:ℝ))‖ ≤
          A*(U/(1+|Z|)+U^(1-δ)) := by
  obtain ⟨C,η,hC,hη,hbound⟩ := logarithmic_phase_uniform B hB
  let δ := min η (1/2:ℝ)
  have hδ : 0 < δ := lt_min hη (by norm_num)
  have hδη : δ ≤ η := min_le_left _ _
  have hδhalf : δ ≤ 1/2 := min_le_right _ _
  refine ⟨max C 2000,δ,lt_of_lt_of_le hC (le_max_left _ _),hδ,hδhalf,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with U hu hU
  intro Z L R hZ hL hR
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hpow : 0 ≤ U^(1-δ) := Real.rpow_nonneg hU0.le _
  have hfrac : 0 ≤ U/(1+|Z|) := by positivity
  have hmaxC : C ≤ max C 2000 := le_max_left _ _
  have hmax2 : (2000:ℝ) ≤ max C 2000 := le_max_right _ _
  by_cases hlo : U^(1/2:ℝ) ≤ |Z|
  · have hraw := hu 0 Z (L:ℤ) (R:ℤ) hlo hZ
      (by simpa only [Int.cast_natCast] using hL)
      (by simpa only [Int.cast_natCast] using hR)
    have hsum : (∑ n ∈ Finset.Icc L R, ExponentialSum.phase (Z*Real.log (n:ℝ))) =
        ∑ n ∈ Finset.Icc (L:ℤ) R, differencingPhase (Z*Real.log (n:ℝ)) := by
      simpa only [Int.cast_natCast, differencingPhase, ExponentialSum.phase] using
        marked_nat_int_interval_sum
          (fun n : ℤ => differencingPhase (Z*Real.log (n:ℝ))) L R
    rw [hsum]
    have hpowers : U^(1-η) ≤ U^(1-δ) :=
      Real.rpow_le_rpow_of_exponent_le hU (by linarith)
    calc
      _ ≤ C*U^(1-η) := by simpa only [zero_mul,zero_add] using hraw
      _ ≤ C*U^(1-δ) := mul_le_mul_of_nonneg_left hpowers hC.le
      _ ≤ (max C 2000)*U^(1-δ) := mul_le_mul_of_nonneg_right hmaxC hpow
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith)
        (le_trans hC.le hmaxC)
  · have hZU : |Z| ≤ U := (le_of_not_ge hlo).trans
      (by simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hU (show (1/2:ℝ) ≤ 1 by norm_num))
    have hsqrt : Real.sqrt |Z| ≤ U^(1-δ) := by
      calc
        _ ≤ Real.sqrt U := Real.sqrt_le_sqrt hZU
        _ = U^(1/2:ℝ) := Real.sqrt_eq_rpow U
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
    calc
      _ ≤ 2000*(U/(1+|Z|)+Real.sqrt |Z|) := log_phase_sharp_bound hU Z L R hL hR
      _ ≤ 2000*(U/(1+|Z|)+U^(1-δ)) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right hmax2 (add_nonneg hfrac hpow)

theorem markedLogKernel_phase (L R : ℕ) (t : ℝ) :
    markedLogKernel L R t =
      ∑ n ∈ Finset.Icc L R, ExponentialSum.phase ((t/(2*Real.pi))*Real.log (n:ℝ)) := by
  unfold markedLogKernel
  apply Finset.sum_congr rfl
  intro n _
  unfold markedPrimePhase ExponentialSum.phase
  congr 2
  push_cast
  field_simp

/-- Every fixed polynomial frequency range admits reciprocal decay plus
a positive power saving. This includes the diagonal without a special case. -/
theorem markedLogKernel_reciprocal_power (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1/2 ∧
      ∀ᶠ U : ℝ in atTop, ∀ (t : ℝ) (L R : ℕ),
        |t| ≤ U^B → U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        ‖markedLogKernel L R t‖ ≤ A*(U/(1+|t|)+U^(1-δ)) := by
  obtain ⟨A,δ,hA,hδ,hδhalf,hbound⟩ := marked_log_phase_reciprocal_power B hB
  refine ⟨8*A,δ,by positivity,hδ,hδhalf,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with U hu hU
  intro t L R ht hL hR
  have hpi : (1:ℝ) ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have hpi8 : 2*Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
  have hpi0 : 0 < 2*Real.pi := by positivity
  have harg : |t/(2*Real.pi)| = |t|/(2*Real.pi) := by
    rw [abs_div,abs_of_pos hpi0]
  have hz : |t/(2*Real.pi)| ≤ U^B := by
    rw [harg]
    exact (div_le_self (abs_nonneg _) hpi).trans ht
  have hfrac : U/(1+|t|/(2*Real.pi)) ≤ 8*(U/(1+|t|)) := by
    have hh : U/(1+|t|/(2*Real.pi)) ≤ (2*Real.pi)*(U/(1+|t|)) := by
      rw [show (2*Real.pi)*(U/(1+|t|)) = ((2*Real.pi)*U)/(1+|t|) by ring]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have he : (2*Real.pi)*U*(1+|t|/(2*Real.pi)) = U*(2*Real.pi+|t|) := by
        field_simp
      rw [he]
      nlinarith
    exact hh.trans (mul_le_mul_of_nonneg_right hpi8 (by positivity))
  rw [markedLogKernel_phase]
  calc
    _ ≤ A*(U/(1+|t/(2*Real.pi)|)+U^(1-δ)) := hu _ _ _ hz hL hR
    _ ≤ A*(8*(U/(1+|t|))+U^(1-δ)) := by rw [harg]; gcongr
    _ ≤ _ := by nlinarith [Real.rpow_nonneg (show 0 ≤ U by linarith) (1-δ)]

/-- The actual dyadic kernel has a logarithmic Gram row bound, with a
power-saving remainder proportional to the number of sample points. -/
theorem markedLogKernel_rows (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1/2 ∧
      ∀ᶠ U : ℝ in atTop, ∀ (L R : ℕ) (S : Finset ℝ) (T : ℝ),
        U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U → 0 ≤ T → T ≤ U^B →
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) →
        (∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ T) →
        ∀ t ∈ S, (∑ u ∈ S, ‖markedLogKernel L R (t-u)‖) ≤
          A*(2*U*(1+Real.log (T+1))+(S.card:ℝ)*U^(1-δ)) := by
  obtain ⟨A,δ,hA,hδ,hδhalf,hbound⟩ := markedLogKernel_reciprocal_power B hB
  refine ⟨A,δ,hA,hδ,hδhalf,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with U hu hU
  intro L R S T hL hR hT hTU hsep hdiam t ht
  exact markedLogKernel_row_of_pointwise L R U A (U^(1-δ)) T
    (by linarith) hA.le hT S hsep
    (fun v hv => hu v L R (hv.trans hTU) hL hR) hdiam t ht

end
end ArtinMatthews
