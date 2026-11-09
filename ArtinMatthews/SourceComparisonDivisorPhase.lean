module

public import ArtinMatthews.SourceComparisonPeriodicPhase
public import ArtinMatthews.MarkedMajorArcDivisorAssembly
public import ArtinMatthews.MarkedMajorArcProductPolynomial


set_option backward.privateInPublic true
@[expose] public section

/-! The actual truncated divisor model on a residue-restricted dyad. -/

namespace ArtinMatthews

open Finset OAI.Problem337

noncomputable section

/-- Express the phase convention in the normalization used by the
logarithmic exponential-sum estimates. -/
theorem sourceComparisonPrimePhase_eq_log_phase (n : ℕ) (t : ℝ) :
    markedPrimePhase n t = ExponentialSum.phase ((t/(2*Real.pi))*Real.log (n:ℝ)) := by
  unfold markedPrimePhase ExponentialSum.phase
  congr 2
  push_cast
  field_simp

/-- Factor an individual divisor exactly, retaining the periodic weight on
its actual multiples. -/
theorem sourceComparisonDivisorPhase_reindex {q : ℕ} (w : ZMod q → ℂ)
    (t : ℝ) {d : ℕ} (hd : 0 < d) (M N : ℕ) :
    (∑ n ∈ Ioc M N, if d ∣ n then w (n:ZMod q)*markedPrimePhase n t else 0) =
      markedPrimePhase d t *
        ∑ m ∈ Icc (M/d+1) (N/d), w ((d:ZMod q)*(m:ZMod q))*markedPrimePhase m t := by
  rw [marked_sum_Ioc_dvd_reindex hd, mul_sum]
  have hI : Ioc (M/d) (N/d) = Icc (M/d+1) (N/d) := by ext n; simp
  rw [hI]
  apply sum_congr rfl
  intro m hm
  have hm0 : 0 < m := (Nat.zero_lt_succ (M/d)).trans_le (mem_Icc.mp hm).1
  rw [Nat.cast_mul, ← markedPrimePhase_mul hd hm0]
  ring

private theorem divisor_dyad_scale {H : ℝ} {d : ℕ} (hd : 0 < d)
    {M N : ℕ} (hM : H ≤ (M:ℝ)+1) (hN : (N:ℝ) ≤ 2*H) :
    H/d ≤ ((M/d+1:ℕ):ℝ) ∧ ((N/d:ℕ):ℝ) ≤ 2*(H/d) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  constructor
  · apply (div_le_iff₀ hdR).2
    have hm : M < (M/d+1)*d := (Nat.div_lt_iff_lt_mul hd).1 (Nat.lt_succ_self (M/d))
    have hmR : (M:ℝ)+1 ≤ ((M/d+1:ℕ):ℝ)*(d:ℝ) := by exact_mod_cast hm
    exact hM.trans hmR
  · calc
      _ ≤ (N:ℝ)/(d:ℝ) := Nat.cast_div_le
      _ ≤ (2*H)/(d:ℝ) := div_le_div_of_nonneg_right hN hdR.le
      _ = _ := by ring

private theorem divisor_model_phase_le {ι : Type*} {q : ℕ}
    (J : Finset ι) (d : ι → ℕ) (c : ι → ℂ) (w : ZMod q → ℂ)
    (M N : ℕ) (H t B : ℝ) (hH : 0 < H) (hd : ∀ i ∈ J, 0 < d i)
    (hbound : ∀ i ∈ J, ‖∑ m ∈ Icc (M/d i+1) (N/d i),
      w ((d i:ZMod q)*(m:ZMod q))*markedPrimePhase m t‖ ≤ B*(H/d i)) :
    ‖markedDyadicPolynomial (M+1) N H
      (fun n => markedMajorDivisorPolynomial J d c n * w (n:ZMod q)) t‖ ≤
      B*(∑ i ∈ J, ‖c i‖/(d i:ℝ)) := by
  have hI : Icc (M+1) N = Ioc M N := by ext n; simp
  have he : (∑ n ∈ Ioc M N,
      (markedMajorDivisorPolynomial J d c n*w (n:ZMod q))*markedPrimePhase n t) =
      ∑ i ∈ J, c i*(∑ n ∈ Ioc M N,
        if d i ∣ n then w (n:ZMod q)*markedPrimePhase n t else 0) := by
    classical
    simp only [markedMajorDivisorPolynomial, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [mul_sum]
    apply sum_congr rfl
    intro n _
    split_ifs <;> simp [mul_assoc]
  rw [markedDyadicPolynomial, hI, he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  apply (div_le_iff₀ hH).mpr
  calc
    _ ≤ ∑ i ∈ J, ‖c i*(∑ n ∈ Ioc M N,
        if d i ∣ n then w (n:ZMod q)*markedPrimePhase n t else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ J, B*(‖c i‖/(d i:ℝ))*H := by
      apply sum_le_sum
      intro i hi
      rw [sourceComparisonDivisorPhase_reindex w t (hd i hi), norm_mul, norm_mul,
        markedPrimePhase_norm, one_mul]
      exact (mul_le_mul_of_nonneg_left (hbound i hi) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := by rw [← sum_mul, ← mul_sum]

/-- Reciprocal-frequency decay for the exact truncated model at moderate
time, with the actual absolute reciprocal divisor mass. -/
theorem sourceComparisonDivisorPhase_moderate {ι : Type*} {q : ℕ} [NeZero q]
    (J : Finset ι) (d : ι → ℕ) (c : ι → ℂ) (w : ZMod q → ℂ)
    (hw : ∀ n, ‖w n‖ ≤ 1) (M N : ℕ) (H t : ℝ)
    (hH : 0 < H) (ht : t ≠ 0) (hM : H ≤ (M:ℝ)+1) (hN : (N:ℝ) ≤ 2*H)
    (hd : ∀ i ∈ J, 0 < d i ∧ 1 ≤ H/d i ∧ 4*(q:ℝ)*|t/(2*Real.pi)| ≤ H/d i) :
    ‖markedDyadicPolynomial (M+1) N H
      (fun n => markedMajorDivisorPolynomial J d c n * w (n:ZMod q)) t‖ ≤
      ((q:ℝ)*16*Real.pi/|t|)*(∑ i ∈ J, ‖c i‖/(d i:ℝ)) := by
  apply divisor_model_phase_le J d c w M N H t _ hH (fun i hi => (hd i hi).1)
  intro i hi
  obtain ⟨hdi, hscale, hfreq⟩ := hd i hi
  obtain ⟨hl, hr⟩ := divisor_dyad_scale hdi hM hN
  have hpi : 0 < 2*Real.pi := by positivity
  simp_rw [sourceComparisonPrimePhase_eq_log_phase]
  refine (sourceComparisonPeriodic_phase_moderate (fun n => w ((d i:ZMod q)*n))
    (fun n => hw _) hscale (div_ne_zero ht hpi.ne') hfreq _ _ hl hr).trans_eq ?_
  rw [abs_div, abs_of_pos hpi]
  have habs : |t| ≠ 0 := abs_ne_zero.mpr ht
  field_simp
  ring

/-- Uniform large-time phase bound for the exact same truncated model. -/
theorem sourceComparisonDivisorPhase_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ U₀ : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1/2 ∧ 0 < U₀ ∧
      ∀ {ι : Type*} (J : Finset ι) (d : ι → ℕ) (c : ι → ℂ)
        (q : ℕ) [NeZero q] (w : ZMod q → ℂ) (M N : ℕ) (H t S : ℝ),
        (∀ n, ‖w n‖ ≤ 1) → 0 < H → U₀ ≤ S → 1 ≤ |t/(2*Real.pi)| →
        H ≤ (M:ℝ)+1 → (N:ℝ) ≤ 2*H →
        (∀ i ∈ J, 0 < d i ∧ S ≤ H/d i ∧ |t/(2*Real.pi)| ≤ (H/d i)^B) →
        ‖markedDyadicPolynomial (M+1) N H
          (fun n => markedMajorDivisorPolynomial J d c n * w (n:ZMod q)) t‖ ≤
          ((q:ℝ)*A*(1/Real.sqrt |t/(2*Real.pi)|+S^(-δ))) *
            (∑ i ∈ J, ‖c i‖/(d i:ℝ)) := by
  obtain ⟨A,δ,U₀,hA,hδ,hδhalf,hU₀,hbound⟩ := sourceComparisonPeriodic_phase_uniform B hB
  refine ⟨A,δ,U₀,hA,hδ,hδhalf,hU₀,?_⟩
  intro ι J d c q _ w M N H t S hw hH hUS ht hM hN hd
  apply divisor_model_phase_le J d c w M N H t _ hH (fun i hi => (hd i hi).1)
  intro i hi
  obtain ⟨hdi, hscale, hfreq⟩ := hd i hi
  obtain ⟨hl, hr⟩ := divisor_dyad_scale hdi hM hN
  have hdiR : (0:ℝ) < d i := by exact_mod_cast hdi
  have hp := marked_scaled_power_reciprocal_bound hH hdiR (hU₀.trans_le hUS) hscale hδ.le
  simp_rw [sourceComparisonPrimePhase_eq_log_phase]
  calc
    _ ≤ (q:ℝ)*A*((H/d i)/Real.sqrt |t/(2*Real.pi)|+(H/d i)^(1-δ)) :=
      hbound q (fun n => w ((d i:ZMod q)*n)) (H/d i) _ _ _
        (fun n => hw _) (hUS.trans hscale) ht hfreq hl hr
    _ ≤ (q:ℝ)*A*((H/d i)/Real.sqrt |t/(2*Real.pi)|+(H/d i)*S^(-δ)) := by
      gcongr
    _ = _ := by ring

end
end ArtinMatthews
