module

public import ArtinMatthews.ShiftedArithmeticSum


set_option backward.privateInPublic true
@[expose] public section

/-! The two arithmetic weights in the off-diagonal correlation estimate. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem shiftedActualPairs_first_contribution (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ,
      (∑ d ∈ Finset.Icc 1 B, ∑ D ∈ shiftedAdmissibleParts B d,
        ((shiftedActualPairs B d D).card : ℝ) * (D : ℝ) / Real.sqrt d) ≤
      C * (B : ℝ)^(2+ε) := by
  obtain ⟨C, hC, hsum⟩ := shiftedActualPairs_weighted_sum (3/2) ε hε (by linarith)
  refine ⟨C,hC,?_⟩
  intro B
  convert hsum B using 1
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro D _hD
  rw [show (1-(3/2) : ℝ) = -(1/2) by norm_num,
    Real.rpow_neg (Nat.cast_nonneg d), ← Real.sqrt_eq_rpow, div_eq_mul_inv]

theorem shiftedActualPairs_quarter_weight (B d D : ℕ) (hd : 0<d)
    (hD : D ∈ shiftedAdmissibleParts B d) :
    ((shiftedActualPairs B d D).card : ℝ) * (D : ℝ)^(1/4 : ℝ) ≤
    ((shiftedActualPairs B d D).card : ℝ) * (D : ℝ) * (d : ℝ)^(1-7/4 : ℝ) := by
  obtain ⟨hDs, hdD⟩ := Finset.mem_filter.mp hD
  have hDpos : 0<D := (Finset.mem_Icc.mp (Finset.mem_filter.mp hDs).1).1
  have hdr : (0 : ℝ)<d := by exact_mod_cast hd
  have hDr : (0 : ℝ)<D := by exact_mod_cast hDpos
  have hle : (d : ℝ)≤D := by exact_mod_cast Nat.le_of_dvd hDpos hdD
  have hpow : (D : ℝ)^(1/4 : ℝ) ≤ (D : ℝ)*(d : ℝ)^(1-7/4 : ℝ) := by
    calc
      _ = (D : ℝ)*(D : ℝ)^(1-7/4 : ℝ) := by
        calc
          _ = (D : ℝ)^(1+(1-7/4) : ℝ) := by norm_num
          _ = _ := by rw [Real.rpow_add hDr, Real.rpow_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hdr hle (by norm_num)) hDr.le
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)

/-- The second spectral term is summable with the larger exponent 7/4.
The comparison uses the proved divisibility d | D, hence D ≥ d. -/
theorem shiftedActualPairs_second_contribution (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε < 3/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ,
      (∑ d ∈ Finset.Icc 1 B, ∑ D ∈ shiftedAdmissibleParts B d,
        ((shiftedActualPairs B d D).card : ℝ) * (D : ℝ)^(1/4 : ℝ)) ≤
      C * (B : ℝ)^(2+ε) := by
  obtain ⟨C,hC,hsum⟩ := shiftedActualPairs_weighted_sum (7/4) ε hε (by linarith)
  refine ⟨C,hC,?_⟩
  intro B
  apply le_trans _ (hsum B)
  apply Finset.sum_le_sum
  intro d hd
  apply Finset.sum_le_sum
  intro D hD
  exact shiftedActualPairs_quarter_weight B d D (Finset.mem_Icc.mp hd).1 hD

end ArtinMatthews
