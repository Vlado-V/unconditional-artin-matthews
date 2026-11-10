module

public import ArtinMatthews.SpectralDyadicPartition
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! The exact finite partial partition of the actual smooth dual windows,
and the signed dyadic geometry used for their frequency blocks. -/

noncomputable section
namespace ArtinMatthews

/-- Partial weight of the two interlaced smooth dyadic families. -/
def shiftedABLDualPartial (J k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (J+1), spectralDyadicBlock j k

theorem shiftedABLDualPartial_bounds (J k : ℕ) :
    0 ≤ shiftedABLDualPartial J k ∧ shiftedABLDualPartial J k ≤ 1 := by
  have hstep (x : ℝ) : 0 ≤ spectralDyadicStep x ∧ spectralDyadicStep x ≤ 1 := by
    constructor
    · by_cases h : x ≤ 1
      · rw [spectralDyadicStep_zero h]
      · simpa only [spectralDyadicStep_zero (le_refl 1)] using
          spectralDyadicStep_monotone (le_of_not_ge h)
    · by_cases h : spectralDyadicRatio ≤ x
      · rw [spectralDyadicStep_one h]
      · simpa only [spectralDyadicStep_one (le_refl spectralDyadicRatio)] using
          spectralDyadicStep_monotone (le_of_not_ge h)
  refine ⟨Finset.sum_nonneg (fun j _ => spectralDyadicBlock_nonneg _ _), ?_⟩
  rw [shiftedABLDualPartial, spectralDyadicBlock_partial_sum]
  exact (sub_le_self _ (hstep _).1).trans (hstep _).2

theorem shiftedABLDualPartial_eq_one {J k : ℕ} (hk : 1 ≤ k)
    (hJ : (k : ℝ) ≤ (2 : ℝ)^J) :
    shiftedABLDualPartial J k = 1 :=
  spectralDyadicBlock_partition k J hk hJ

/-- The chosen dyadic height reaches the cutoff while staying within a
factor of two of it. -/
def shiftedABLDualCutoffIndex (L : ℝ) : ℕ := Nat.log 2 ⌊L⌋₊ + 1

theorem shiftedABLDualCutoffIndex_bounds {L : ℝ} (hL : 1 ≤ L) :
    L ≤ (2 : ℝ)^(shiftedABLDualCutoffIndex L) ∧
      (2 : ℝ)^(shiftedABLDualCutoffIndex L) ≤ 2*L := by
  let K := ⌊L⌋₊
  have hK : 1 ≤ K := (Nat.le_floor_iff (by linarith)).2 (by simpa using hL)
  have hup : (K : ℝ) ≤ L := Nat.floor_le (by linarith)
  have hhi : K + 1 ≤ 2^(Nat.log 2 K+1) := Nat.lt_pow_succ_log_self (by decide) _
  have hhi' : (K : ℝ) + 1 ≤ (2 : ℝ)^(Nat.log 2 K+1) := by exact_mod_cast hhi
  have hlo : (2 : ℝ)^(Nat.log 2 K) ≤ K := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : K ≠ 0)
  change L ≤ (2 : ℝ)^(Nat.log 2 K+1) ∧ (2 : ℝ)^(Nat.log 2 K+1) ≤ 2*L
  exact ⟨(Nat.lt_floor_add_one L).le.trans hhi', by rw [pow_succ]; linarith⟩

/-- A genuine nonzero sample of the two interlaced windows is comparable
to its exact scale. -/
theorem shiftedABLDualWindow_bounds {j k : ℕ} (h : spectralDyadicBlock j k ≠ 0) :
    (2 : ℝ)^j ≤ 2*(k : ℝ) ∧ (k : ℝ) ≤ 2*(2 : ℝ)^j := by
  let K : ℝ := 2^j
  have hK : 0 < K := by positivity
  have hr := spectralDyadicRatio_one_lt
  have hr2 : spectralDyadicRatio ≤ 2 := by
    nlinarith [spectralDyadicRatio_sq, sq_nonneg (spectralDyadicRatio-1)]
  change spectralDyadicWeight ((k : ℝ)/K) +
    spectralDyadicWeight (spectralDyadicRatio*(k : ℝ)/K) ≠ 0 at h
  by_cases h₁ : spectralDyadicWeight ((k : ℝ)/K) = 0
  · have h₂ : spectralDyadicWeight (spectralDyadicRatio*(k : ℝ)/K) ≠ 0 := by
      simpa only [h₁, zero_add] using h
    obtain ⟨hl,hu⟩ := spectralDyadicWeight_support h₂
    have hlow := (le_div_iff₀ hK).1 hl
    have hhigh := (div_le_iff₀ hK).1 hu
    exact ⟨(by simpa only [one_mul] using hlow :
      K ≤ spectralDyadicRatio*(k : ℝ)).trans
        (mul_le_mul_of_nonneg_right hr2 (Nat.cast_nonneg _)),
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hr.le (Nat.cast_nonneg k) :
        (k : ℝ) ≤ spectralDyadicRatio*(k : ℝ)).trans hhigh⟩
  · obtain ⟨hl,hu⟩ := spectralDyadicWeight_support h₁
    have hlow := (le_div_iff₀ hK).1 hl
    have hhigh := (div_le_iff₀ hK).1 hu
    exact ⟨by linarith [Nat.cast_nonneg (α := ℝ) k], hhigh⟩

/-- The sharp frequency partition is a partition of the coefficient
indices. The sign and the absolute value remain separate. -/
theorem shiftedABLFrequency_dyadic {ρ : ℤ} (hρ : ρ ≠ 0) :
    2^(Nat.log 2 ρ.natAbs) ≤ ρ.natAbs ∧
      ρ.natAbs < 2^(Nat.log 2 ρ.natAbs+1) :=
  ⟨Nat.pow_log_le_self 2 (Int.natAbs_ne_zero.mpr hρ),
    Nat.lt_pow_succ_log_self (by decide) _⟩

end ArtinMatthews
