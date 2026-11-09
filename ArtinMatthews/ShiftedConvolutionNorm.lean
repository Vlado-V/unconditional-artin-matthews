module

public import ArtinMatthews.ShiftedConvolutionWeights
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


set_option backward.privateInPublic true
@[expose] public section

/-!
# Equation (5.6) for the actual cusp-form convolution

Both weights are fixed smooth dyadic cutoffs. The norm bound is uniform in the
Mellin heights, the positive convolution frequencies, and the congruence modulus.
The proof retains the normalized character average and therefore has no D loss.
-/

noncomputable section
open Complex UpperHalfPlane Real Set Finset
open scoped ContDiff

namespace ArtinMatthews

/-- The literal Aρ with coefficients of an actual cusp form, dyadic cutoffs,
and the two Mellin-height factors. -/
def dyadicCuspConvolution {Γ : Subgroup (GL (Fin 2) ℝ)} (f : CuspForm Γ 1)
    (w1 w2 : ℝ → ℂ) (K1 K2 t1 t2 : ℝ) (m3 m4 D : ℕ) (r : ℤ) : ℂ :=
  shiftedConvolutionCoeff (range (shiftedDyadicLength K1)) (range (shiftedDyadicLength K2))
    m3 m4 D (fun k ↦ (qExpansion 1 f).coeff k * shiftedDyadicWeight w1 K1 t1 k)
      (fun k ↦ (qExpansion 1 f).coeff k * shiftedDyadicWeight w2 K2 t2 k) r

private theorem dyadic_log_sq_le (K ν : ℝ) (hK : 1 ≤ K) (hν : 0 < ν) :
    Real.log (2 * (shiftedDyadicLength K : ℝ)) ^ 2 ≤
      (8 ^ (ν / 2) / (ν / 2)) ^ 2 * K ^ ν := by
  have hK0 : 0 < K := by linarith
  have hN := shiftedDyadicLength_bounds K hK
  have hN0 : (0 : ℝ) < shiftedDyadicLength K := by exact_mod_cast (by omega : 0 < shiftedDyadicLength K)
  have hlog0 : 0 ≤ Real.log (2 * (shiftedDyadicLength K : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * shiftedDyadicLength K))
  have hlog : Real.log (2 * (shiftedDyadicLength K : ℝ)) ≤
      (8 ^ (ν / 2) / (ν / 2)) * K ^ (ν / 2) := by
    calc
      _ ≤ Real.log (8 * K) := Real.log_le_log (by positivity) (by linarith [hN.2])
      _ ≤ (8 * K) ^ (ν / 2) / (ν / 2) := Real.log_le_rpow_div (by positivity) (by linarith)
      _ = _ := by rw [Real.mul_rpow (by norm_num) hK0.le]; ring
  apply (pow_le_pow_left₀ hlog0 hlog 2).trans_eq
  rw [mul_pow, ← Real.rpow_natCast (K ^ (ν / 2)) 2, ← Real.rpow_mul hK0.le]
  norm_num

/-- Squared coefficient norm, with a stronger time dependence than (5.6).
The positive second frequency is needed only to prevent collisions in its Parseval identity. -/
theorem weightOne_dyadicConvolution_energy
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods)
    (w1 w2 : SchwartzMap ℝ ℂ) (hw1 : Function.support w1 ⊆ Icc 1 2)
    (ν : ℝ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K1 K2 t1 t2 : ℝ), 1 ≤ K1 → 1 ≤ K2 →
      ∀ (m3 m4 D : ℕ) [NeZero D], 0 < m4 →
        (∑' r : ℤ, ‖dyadicCuspConvolution f w1 w2 K1 K2 t1 t2 m3 m4 D r‖ ^ 2) ≤
          C * (K1 * K2) ^ (1 + ν) * (1 + |t1|) ^ 2 := by
  obtain ⟨C0, hC0, hbase⟩ := weightOne_shiftedConvolution_energy f hperiod
  let A := 9 * SchwartzMap.seminorm ℝ 0 0 w1 + 4 * SchwartzMap.seminorm ℝ 0 1 w1
  let B := SchwartzMap.seminorm ℝ 0 0 w2
  let E := (8 : ℝ) ^ (ν / 2) / (ν / 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := apply_nonneg _ _
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨16 * C0 * E ^ 2 * A ^ 2 * B ^ 2, by positivity, ?_⟩
  intro K1 K2 t1 t2 hK1 hK2 m3 m4 D inst hm4
  have hK10 : 0 < K1 := by linarith
  have hK20 : 0 < K2 := by linarith
  have hN1 := shiftedDyadicLength_bounds K1 hK1
  have hN2 := shiftedDyadicLength_bounds K2 hK2
  have hvar := shiftedDyadicWeight_variation w1 hw1 K1 t1 hK1
  have hlog := dyadic_log_sq_le K1 ν hK1 hν
  have hvar0 : 0 ≤ sampledVariation (shiftedDyadicLength K1)
      (shiftedDyadicWeight w1 K1 t1) := by
    unfold sampledVariation
    positivity
  have hpow : K1 ^ ν ≤ (K1 * K2) ^ ν :=
    Real.rpow_le_rpow hK10.le (by nlinarith) hν.le
  apply Real.tsum_le_of_sum_le (fun _ ↦ sq_nonneg _)
  intro R
  have hb := hbase (shiftedDyadicLength K1) (shiftedDyadicLength K2) m3 m4 D hN1.1 hm4
    (shiftedDyadicWeight w1 K1 t1) (shiftedDyadicWeight w2 K2 t2) B hB
    (fun k _ ↦ by
      simpa only [shiftedDyadicWeight, norm_mul, norm_shiftedMellinPhase, one_mul] using
        SchwartzMap.norm_le_seminorm ℝ w2 ((k : ℝ) / K2)) R
  apply hb.trans
  calc
    _ ≤ C0 * (4 * K1) * (4 * K2) * (E ^ 2 * K1 ^ ν) *
        (A * (1 + |t1|)) ^ 2 * B ^ 2 := by
      gcongr <;> first | exact hN1.2 | exact hN2.2
    _ = (16 * C0 * E ^ 2 * A ^ 2 * B ^ 2) * (K1 * K2) * K1 ^ ν * (1 + |t1|) ^ 2 := by ring
    _ ≤ (16 * C0 * E ^ 2 * A ^ 2 * B ^ 2) * (K1 * K2) * (K1 * K2) ^ ν * (1 + |t1|) ^ 2 := by
      gcongr
    _ = _ := by rw [Real.rpow_add (mul_pos hK10 hK20), Real.rpow_one]; ring

/-- Equation (5.6): the actual ℓ² norm, uniformly in the congruence modulus D.
A second-cutoff support hypothesis is not needed for this bound, since only its supremum is used. -/
theorem weightOne_dyadicConvolution_norm
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods)
    (w1 w2 : SchwartzMap ℝ ℂ) (hw1 : Function.support w1 ⊆ Icc 1 2)
    (ν : ℝ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K1 K2 t1 t2 : ℝ), 1 ≤ K1 → 1 ≤ K2 →
      ∀ (m3 m4 D : ℕ) [NeZero D], 0 < m4 →
        Real.sqrt (∑' r : ℤ, ‖dyadicCuspConvolution f w1 w2 K1 K2 t1 t2 m3 m4 D r‖ ^ 2) ≤
          C * (K1 * K2) ^ ((1 + ν) / 2) * (1 + |t1| + |t2|) ^ 2 := by
  obtain ⟨C0, hC0, hb⟩ := weightOne_dyadicConvolution_energy f hperiod w1 w2 hw1 ν hν
  refine ⟨Real.sqrt C0, Real.sqrt_nonneg _, ?_⟩
  intro K1 K2 t1 t2 hK1 hK2 m3 m4 D inst hm4
  have hK : 0 < K1 * K2 := by positivity
  have ht : 0 ≤ 1 + |t1| + |t2| := by positivity
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  apply (hb K1 K2 t1 t2 hK1 hK2 m3 m4 D hm4).trans
  have hpower : ((K1 * K2) ^ ((1 + ν) / 2)) ^ 2 = (K1 * K2) ^ (1 + ν) := by
    rw [← Real.rpow_natCast ((K1 * K2) ^ ((1 + ν) / 2)) 2, ← Real.rpow_mul hK.le]
    norm_num
  rw [mul_pow, mul_pow, Real.sq_sqrt hC0, hpower]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hh : 1 + |t1| ≤ (1 + |t1| + |t2|) ^ 2 := by nlinarith [abs_nonneg t1, abs_nonneg t2]
  exact pow_le_pow_left₀ (by positivity) hh 2

end ArtinMatthews
