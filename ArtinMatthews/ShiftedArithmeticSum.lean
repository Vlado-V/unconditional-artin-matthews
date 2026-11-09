module

public import ArtinMatthews.ShiftedPairCountActual
public import ArtinMatthews.ShiftedSmoothWeighted


set_option backward.privateInPublic true
@[expose] public section

/-! Actual grouped off-diagonal arithmetic sums for §5.3. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

def shiftedAdmissibleParts (B d : ℕ) : Finset ℕ :=
  (shiftedSmoothSet B d.primeFactors).filter (d ∣ ·)

theorem shiftedActualPairs_weighted_part (B d D : ℕ) (hd : 0 < d)
    (hD : D ∈ shiftedAdmissibleParts B d) (α : ℝ) :
    ((shiftedActualPairs B d D).card : ℝ) * (D : ℝ) * (d : ℝ)^(1-α) ≤
      2*(B : ℝ)^2*(d : ℝ)^(-α) := by
  obtain ⟨hDs, hdD⟩ := Finset.mem_filter.mp hD
  have hDpos : 0 < D := (Finset.mem_Icc.mp (Finset.mem_filter.mp hDs).1).1
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hDr : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hp : (d : ℝ)^(1-α) = (d : ℝ)*(d : ℝ)^(-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hdr, Real.rpow_one]
  have hbound := mul_le_mul_of_nonneg_right
    (shiftedActualPairs_card_real B d D hd hDpos hdD)
    (mul_nonneg hDr.le (Real.rpow_nonneg hdr.le (1-α)))
  calc
    _ ≤ (2*(B : ℝ)^2/((d : ℝ)*(D : ℝ))) * ((D : ℝ)*(d : ℝ)^(1-α)) := by
      simpa only [mul_assoc] using hbound
    _ = _ := by rw [hp]; field_simp

theorem shiftedActualPairs_weighted_parts (B d : ℕ) (hd : 0 < d) (α : ℝ) :
    (∑ D ∈ shiftedAdmissibleParts B d,
      ((shiftedActualPairs B d D).card : ℝ) * (D : ℝ) * (d : ℝ)^(1-α)) ≤
    2*(B : ℝ)^2 *
      (((shiftedSmoothSet B d.primeFactors).card : ℝ) * (d : ℝ)^(-α)) := by
  calc
    _ ≤ ∑ _D ∈ shiftedAdmissibleParts B d, 2*(B : ℝ)^2*(d : ℝ)^(-α) :=
      Finset.sum_le_sum (fun D hD => shiftedActualPairs_weighted_part B d D hd hD α)
    _ = 2*(B : ℝ)^2 *
        (((shiftedAdmissibleParts B d).card : ℝ)*(d : ℝ)^(-α)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      exact_mod_cast Finset.card_filter_le (shiftedSmoothSet B d.primeFactors) (d ∣ ·)

/-- Uniform bound for the actual pair counts with the weight
`D * d^(1-α)`. Taking α=3/2 gives the first spectral contribution. -/
theorem shiftedActualPairs_weighted_sum (α ε : ℝ) (hε : 0 < ε)
    (hα : ε < α-1) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ,
      (∑ d ∈ Finset.Icc 1 B, ∑ D ∈ shiftedAdmissibleParts B d,
        ((shiftedActualPairs B d D).card : ℝ) * (D : ℝ) * (d : ℝ)^(1-α)) ≤
      C * (B : ℝ)^(2+ε) := by
  obtain ⟨C, hC, hsum⟩ := shiftedSmooth_weighted_count α ε hε hα
  refine ⟨2*C, mul_pos (by norm_num) hC, ?_⟩
  intro B
  by_cases hB : B=0
  · subst B
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ)<1), Finset.sum_empty]
    positivity
  have hBr : (0 : ℝ)<B := by exact_mod_cast Nat.pos_of_ne_zero hB
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 B, 2*(B : ℝ)^2 *
        (((shiftedSmoothSet B d.primeFactors).card : ℝ)*(d : ℝ)^(-α)) :=
      Finset.sum_le_sum (fun d hd =>
        shiftedActualPairs_weighted_parts B d (Finset.mem_Icc.mp hd).1 α)
    _ = 2*(B : ℝ)^2 * (∑ d ∈ Finset.Icc 1 B,
        ((shiftedSmoothSet B d.primeFactors).card : ℝ)*(d : ℝ)^(-α)) := by
      rw [Finset.mul_sum]
    _ ≤ 2*(B : ℝ)^2 * (C*(B : ℝ)^ε) :=
      mul_le_mul_of_nonneg_left (hsum B) (by positivity)
    _ = _ := by rw [Real.rpow_add hBr, Real.rpow_two]; ring

end ArtinMatthews
