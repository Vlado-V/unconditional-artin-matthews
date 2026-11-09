module

public import ArtinMatthews.MarkedTypeIIGoodFirst
public import ArtinMatthews.MarkedBonferroniTail


set_option backward.privateInPublic true
@[expose] public section

/-! Literal logarithmic memory cutoff and slot count absorb the actual dirty
row epsilon.  No prime-band exponents enter these numerical estimates. -/
namespace ArtinMatthews
open Filter
open scoped Topology
noncomputable section

def markedDirtyMemoryCutoff (x : ℝ) : ℕ := ⌈(Real.log x) ^ 2⌉₊

def markedDirtyScalarEpsilon (C : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  C * ((markedDirtyMemoryCutoff x : ℝ) * (markedPadSlots x : ℝ)⁻¹ ^ K +
    (markedDirtyMemoryCutoff x : ℝ) ^ K * Real.exp (-((Real.log x) ^ (1 / 10 : ℝ)) / 4))

theorem markedDirtyMemoryCutoff_le {x : ℝ} (hx : 1 ≤ Real.log x) :
    (markedDirtyMemoryCutoff x : ℝ) ≤ 2 * (Real.log x) ^ (2 : ℝ) := by
  have hc := Nat.ceil_lt_add_one (sq_nonneg (Real.log x))
  change (⌈(Real.log x) ^ 2⌉₊ : ℝ) ≤ _
  rw [Real.rpow_two]
  nlinarith

theorem markedPadSlots_inv_pow_le (K : ℕ) {x : ℝ} (hx : 0 < Real.log x) :
    (markedPadSlots x : ℝ)⁻¹ ^ K ≤ (Real.log x) ^ (-(K : ℝ) / 100) := by
  have hm : (Real.log x) ^ (1 / 100 : ℝ) ≤ (markedPadSlots x : ℝ) := by
    simpa only [markedPadSlots, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one ((Real.log x) ^ (1 / 100 : ℝ))).le
  have hb : 0 < (Real.log x) ^ (1 / 100 : ℝ) := Real.rpow_pos_of_pos hx _
  have hmpos : 0 < (markedPadSlots x : ℝ) := hb.trans_le hm
  calc
    _ ≤ ((Real.log x) ^ (1 / 100 : ℝ))⁻¹ ^ K :=
      pow_le_pow_left₀ (inv_nonneg.mpr hmpos.le) ((inv_le_inv₀ hmpos hb).mpr hm) K
    _ = _ := by
      rw [← Real.rpow_neg hx.le, ← Real.rpow_mul_natCast hx.le]
      congr 1
      ring

theorem markedDirtyScalarEpsilon_nonneg {C : ℝ} (hC : 0 ≤ C) (K : ℕ) (x : ℝ) :
    0 ≤ markedDirtyScalarEpsilon C K x := by unfold markedDirtyScalarEpsilon; positivity

theorem markedDirtyScalar_log_envelope {C : ℝ} (hC : 0 ≤ C) (K : ℕ) (A : ℝ)
    {x : ℝ} (hx : 1 ≤ Real.log x) :
    (Real.log x) ^ A * markedDirtyScalarEpsilon C K x ≤
      (2 * C) * (Real.log x) ^ (A + 2 - (K : ℝ) / 100) +
      (C * (2 : ℝ) ^ K) * (Real.log x) ^ (A + 2 * (K : ℝ)) *
        Real.exp (-(1 / 4 : ℝ) * (Real.log x) ^ (1 / 10 : ℝ)) := by
  have hL : 0 < Real.log x := by linarith
  have hB := markedDirtyMemoryCutoff_le hx
  have hM := markedPadSlots_inv_pow_le K hL
  have hBK : (markedDirtyMemoryCutoff x : ℝ) ^ K ≤
      (2 : ℝ) ^ K * (Real.log x) ^ (2 * (K : ℝ)) := by
    calc
      _ ≤ (2 * (Real.log x) ^ (2 : ℝ)) ^ K := pow_le_pow_left₀ (Nat.cast_nonneg _) hB K
      _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hL.le]
  calc
    _ ≤ (Real.log x) ^ A * (C *
        ((2 * (Real.log x) ^ (2 : ℝ)) * (Real.log x) ^ (-(K : ℝ) / 100) +
        ((2 : ℝ) ^ K * (Real.log x) ^ (2 * (K : ℝ))) *
          Real.exp (-((Real.log x) ^ (1 / 10 : ℝ)) / 4))) := by
      unfold markedDirtyScalarEpsilon
      gcongr
    _ = _ := by
      rw [show A + 2 - (K : ℝ) / 100 = (A + 2) + (-(K : ℝ) / 100) by ring,
        Real.rpow_add hL, Real.rpow_add hL, Real.rpow_add hL,
        show -((Real.log x) ^ (1 / 10 : ℝ)) / 4 =
          -(1 / 4 : ℝ) * (Real.log x) ^ (1 / 10 : ℝ) by ring]
      ring

theorem markedDirtyScalar_log_tendsto {C : ℝ} (hC : 0 ≤ C) (K : ℕ) (A : ℝ)
    (hK : 100 * (A + 2) < (K : ℝ)) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A * markedDirtyScalarEpsilon C K x)
      atTop (nhds 0) := by
  have hpow := ((tendsto_rpow_neg_atTop
    (show 0 < (K : ℝ) / 100 - A - 2 by linarith)).const_mul (2 * C)).comp Real.tendsto_log_atTop
  have hexp := ((rpow_mul_exp_neg_rpow_tendsto (A + 2 * (K : ℝ))
    (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
      (C * (2 : ℝ) ^ K)).comp Real.tendsto_log_atTop
  have ht := hpow.add hexp
  simp only [mul_zero, zero_add, Function.comp_def] at ht
  have hneg : -((K : ℝ) / 100 - A - 2) = A + 2 - (K : ℝ) / 100 := by ring
  rw [hneg] at ht
  apply squeeze_zero' ?_ ?_ ht
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hx
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (markedDirtyScalarEpsilon_nonneg hC K x)
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hx
    simpa only [mul_assoc] using markedDirtyScalar_log_envelope hC K A hx

/-- The actual asymmetric-Schur square-root loss still saves the requested
logarithmic power once the integer depth exceeds the stated explicit threshold. -/
theorem markedDirtyScalar_sqrt_log_tendsto {C : ℝ} (hC : 0 ≤ C) (K : ℕ) (A : ℝ)
    (hK : 200 * (A + 1) < (K : ℝ)) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A * Real.sqrt (markedDirtyScalarEpsilon C K x))
      atTop (nhds 0) := by
  have ht := (markedDirtyScalar_log_tendsto hC K (2 * A) (by nlinarith)).sqrt
  rw [Real.sqrt_zero] at ht
  apply ht.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  have hp : (Real.log x) ^ (2 * A) = ((Real.log x) ^ A) ^ 2 := by
    rw [← Real.rpow_mul_natCast hx.le]
    congr 1
    norm_num
    ring
  rw [hp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.rpow_nonneg hx.le _)]

end
end ArtinMatthews
