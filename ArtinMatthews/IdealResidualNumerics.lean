module

public import ArtinMatthews.IdealProbeDecay


set_option backward.privateInPublic true
@[expose] public section

/-! The full comparison-family error and the two survivor terms have
a fixed logarithmic budget independent of the copied dimension. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem idealComparison_count_power (L B : ℝ) (P : ℕ) (hL : 1 ≤ L)
    (hP : (P:ℝ) ≤ B*Real.log L) :
    (2:ℝ)^P ≤ L^(B*Real.log 2) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),
    Real.rpow_def_of_pos hLpos]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hP (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
  nlinarith

theorem idealResidualNorm_absorb (L B E A₀ : ℝ) (P : ℕ)
    (hL : 2 ≤ L) (hP : (P:ℝ) ≤ B*Real.log L)
    (hA : E+B*Real.log 2+3 ≤ A₀) :
    2*L^(-(E+3))+(2:ℝ)^P*L^(-A₀) ≤ L^(-E) := by
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have herr : (2:ℝ)^P*L^(-A₀) ≤ L^(-(E+3)) := by
    calc
      _ ≤ L^(B*Real.log 2)*L^(-A₀) :=
        mul_le_mul_of_nonneg_right (idealComparison_count_power L B P hL1 hP) (Real.rpow_nonneg hLpos.le _)
      _ = L^(B*Real.log 2-A₀) := by rw [sub_eq_add_neg,Real.rpow_add hLpos]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hcube : 3 ≤ L^3 := by nlinarith [sq_nonneg (L-2)]
  have hpow : 0 < L^3 := pow_pos hLpos 3
  have hdelta : L^(-(E+3))=L^(-E)/(L^3) := by
    rw [show -(E+3)= -E-(3:ℝ) by ring,Real.rpow_sub hLpos,Real.rpow_ofNat]
  calc
    _ ≤ 3*L^(-(E+3)) := by linarith
    _ = 3*L^(-E)/(L^3) := by rw [hdelta]; ring
    _ ≤ L^(-E) := (div_le_iff₀ hpow).mpr
      (by nlinarith [Real.rpow_nonneg hLpos.le (-E)])

end
end ArtinMatthews
