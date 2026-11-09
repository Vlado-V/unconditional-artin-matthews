module

public import ArtinMatthews.CubicThetaGammaBalanced


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine generators of the level-three cubic theta invariance subgroup. -/

noncomputable section
open scoped MatrixGroups
namespace ArtinMatthews
open CongruenceSubgroup

/-- The lower level-three unipotent generator. -/
def cubicThetaU3 : SL(2, ℤ) := ⟨!![1, 0; 3, 1], by norm_num [Matrix.det_fin_two]⟩

/-- Its integer one-parameter subgroup. -/
def cubicThetaLower (n : ℤ) : SL(2, ℤ) :=
  ⟨!![1, 0; 3*n, 1], by norm_num [Matrix.det_fin_two]⟩

@[simp] theorem cubicThetaLower_zero : cubicThetaLower 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubicThetaLower]

@[simp] theorem cubicThetaLower_one : cubicThetaLower 1 = cubicThetaU3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubicThetaLower, cubicThetaU3]

theorem cubicThetaLower_add (n m : ℤ) :
    cubicThetaLower (n+m) = cubicThetaLower n * cubicThetaLower m := by
  apply Subtype.ext
  change (!![1, 0; 3*(n+m), 1] : Matrix (Fin 2) (Fin 2) ℤ) =
    !![1, 0; 3*n, 1] * !![1, 0; 3*m, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

@[simp] theorem cubicThetaLower_neg_one : cubicThetaLower (-1) = cubicThetaU3⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  rw [← cubicThetaLower_one, ← cubicThetaLower_add]
  norm_num

theorem cubicThetaLower_mem_of_generator (H : Subgroup SL(2, ℤ))
    (hU : cubicThetaU3 ∈ H) (n : ℤ) : cubicThetaLower n ∈ H := by
  induction n using Int.induction_on with
  | zero => simpa only [cubicThetaLower_zero] using H.one_mem
  | succ k ih =>
    rw [cubicThetaLower_add, cubicThetaLower_one]
    exact H.mul_mem ih hU
  | pred k ih =>
    rw [show -(k : ℤ)-1 = -(k : ℤ)+(-1) by ring,
      cubicThetaLower_add, cubicThetaLower_neg_one]
    exact H.mul_mem ih (H.inv_mem hU)

theorem cubicTheta_T_mem_Gamma1_three : ModularGroup.T ∈ Gamma1 3 := by
  apply (Gamma1_mem 3 ModularGroup.T).mpr
  norm_num [ModularGroup.T]

theorem cubicThetaLower_mem_Gamma1_three (n : ℤ) : cubicThetaLower n ∈ Gamma1 3 := by
  apply (Gamma1_mem 3 _).mpr
  refine ⟨by rfl, by rfl, ?_⟩
  change ((3*n : ℤ) : ZMod 3) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact dvd_mul_right 3 n

theorem cubicTheta_T_zpow_mul_a (n : ℤ) (γ : SL(2, ℤ)) :
    (ModularGroup.T^n*γ) 0 0 = γ 0 0+n*γ 1 0 := by
  change ((ModularGroup.T^n).val * γ.val) 0 0 = _
  rw [ModularGroup.coe_T_zpow]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem cubicTheta_T_zpow_mul_c (n : ℤ) (γ : SL(2, ℤ)) :
    (ModularGroup.T^n*γ) 1 0 = γ 1 0 := by
  change ((ModularGroup.T^n).val * γ.val) 1 0 = _
  rw [ModularGroup.coe_T_zpow]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem cubicThetaLower_mul_c (n : ℤ) (γ : SL(2, ℤ)) :
    (cubicThetaLower n*γ) 1 0 = γ 1 0+3*n*γ 0 0 := by
  change ((!![1, 0; 3*n, 1] : Matrix (Fin 2) (Fin 2) ℤ) * γ.val) 1 0 = _
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The terminal upper triangular matrix has positive diagonal because it
belongs to Γ₁(3), so it is literally a power of T. -/
theorem Gamma1_three_eq_T_zpow_of_c_zero (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma1 3) (hc : γ 1 0 = 0) : γ = ModularGroup.T^(γ 0 1) := by
  have had : γ 0 0*γ 1 1 = 1 := by
    have hh := γ.det_coe
    simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using hh
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, ModularGroup.coe_T_zpow]
  · have hmod := ((Gamma1_mem 3 γ).mp hγ).1
    rw [ha] at hmod
    exact ((by decide : (-1 : ZMod 3) ≠ 1) hmod).elim

end ArtinMatthews
