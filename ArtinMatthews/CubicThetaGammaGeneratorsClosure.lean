module

public import ArtinMatthews.CubicThetaGammaGenerators


set_option backward.privateInPublic true
@[expose] public section

/-! Balanced Euclidean descent proves the actual level-three generator theorem. -/

noncomputable section
open scoped MatrixGroups
namespace ArtinMatthews
open CongruenceSubgroup

/-- Every subgroup containing the two literal generators contains Γ₁(3). -/
theorem Gamma1_three_le_of_T_U3_mem (H : Subgroup SL(2, ℤ))
    (hT : ModularGroup.T ∈ H) (hU : cubicThetaU3 ∈ H) : Gamma1 3 ≤ H := by
  have hall : ∀ n : ℕ, ∀ γ : SL(2, ℤ), (γ 1 0).natAbs = n →
      γ ∈ Gamma1 3 → γ ∈ H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro γ hn hγ
      by_cases hc : γ 1 0 = 0
      · rw [Gamma1_three_eq_T_zpow_of_c_zero γ hγ hc]
        exact H.zpow_mem hT _
      obtain ⟨k, hk⟩ := exists_balanced_add_mul (γ 0 0) (γ 1 0) hc
      let γ₁ : SL(2, ℤ) := ModularGroup.T^k * γ
      have hγ₁ : γ₁ ∈ Gamma1 3 :=
        (Gamma1 3).mul_mem ((Gamma1 3).zpow_mem cubicTheta_T_mem_Gamma1_three k) hγ
      have hb₁ : 2*|γ₁ 0 0| ≤ |γ 1 0| := by
        simpa only [γ₁, cubicTheta_T_zpow_mul_a] using hk
      have hc₁ : γ₁ 1 0 = γ 1 0 := cubicTheta_T_zpow_mul_c k γ
      have ha₁ : γ₁ 0 0 ≠ 0 := by
        intro hz
        have hh := ((Gamma1_mem 3 γ₁).mp hγ₁).1
        rw [hz] at hh
        exact zero_ne_one hh
      obtain ⟨l, hl⟩ := exists_three_balanced_add_mul (γ₁ 1 0) (γ₁ 0 0) ha₁
      let γ₂ : SL(2, ℤ) := cubicThetaLower l * γ₁
      have hγ₂ : γ₂ ∈ Gamma1 3 :=
        (Gamma1 3).mul_mem (cubicThetaLower_mem_Gamma1_three l) hγ₁
      have hb₂ : 2*|γ₂ 1 0| ≤ 3*|γ₁ 0 0| := by
        simpa only [γ₂, cubicThetaLower_mul_c] using hl
      have hsmallZ : |γ₂ 1 0| < |γ 1 0| := by
        have hpos : 0 < |γ 1 0| := abs_pos.mpr hc
        nlinarith
      have hsmall : (γ₂ 1 0).natAbs < n := by
        rw [← hn]
        have hh : ((γ₂ 1 0).natAbs : ℤ) < ((γ 1 0).natAbs : ℤ) := by
          simpa only [Int.natCast_natAbs] using hsmallZ
        exact_mod_cast hh
      have hγ₂H : γ₂ ∈ H := ih _ hsmall γ₂ rfl hγ₂
      have hstep : cubicThetaLower l * ModularGroup.T^k ∈ H :=
        H.mul_mem (cubicThetaLower_mem_of_generator H hU l) (H.zpow_mem hT k)
      have hh : (cubicThetaLower l * ModularGroup.T^k)⁻¹ * γ₂ ∈ H :=
        H.mul_mem (H.inv_mem hstep) hγ₂H
      have heq : (cubicThetaLower l * ModularGroup.T^k)⁻¹ * γ₂ = γ := by
        dsimp only [γ₂, γ₁]
        group
      rwa [heq] at hh
  intro γ hγ
  exact hall _ γ rfl hγ

/-- The two explicit unipotents genuinely generate the full Γ₁(3). -/
theorem Gamma1_three_eq_closure_T_U3 :
    Gamma1 3 = Subgroup.closure ({ModularGroup.T, cubicThetaU3} : Set SL(2, ℤ)) := by
  apply le_antisymm
  · apply Gamma1_three_le_of_T_U3_mem
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  · apply (Subgroup.closure_le (Gamma1 3)).mpr
    intro γ hγ
    rcases hγ with rfl | rfl
    · exact cubicTheta_T_mem_Gamma1_three
    · change cubicThetaU3 ∈ Gamma1 3
      rw [← cubicThetaLower_one]
      exact cubicThetaLower_mem_Gamma1_three 1

/-- The two signs of Γ₁(3) are exactly Γ₀(3), with no omitted matrix class. -/
theorem Gamma0_three_mem_iff_signed_Gamma1 (γ : SL(2, ℤ)) :
    γ ∈ Gamma0 3 ↔ γ ∈ Gamma1 3 ∨ -γ ∈ Gamma1 3 := by
  constructor
  · intro hγ
    have hc : (γ 1 0 : ZMod 3) = 0 := hγ
    have hdet : (γ 0 0 : ZMod 3)*(γ 1 1 : ZMod 3) = 1 := by
      have hi : γ 0 0*γ 1 1-γ 0 1*γ 1 0 = 1 := by
        simpa only [Matrix.det_fin_two] using γ.det_coe
      have hh := congrArg (fun z : ℤ => (z : ZMod 3)) hi
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, mul_zero] at hh
      linear_combination hh
    have hchoices : ∀ x y : ZMod 3, x*y=1 →
        (x=1 ∧ y=1) ∨ (x=-1 ∧ y=-1) := by decide
    rcases hchoices _ _ hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
    · exact Or.inl ((Gamma1_mem 3 γ).mpr ⟨ha, hd, hc⟩)
    · right
      apply (Gamma1_mem 3 (-γ)).mpr
      simp [ha, hd, hc]
      exact neg_neg (1 : ZMod 3)
  · rintro (hγ | hγ)
    · exact Gamma1_in_Gamma0 3 hγ
    · have hneg := Gamma1_in_Gamma0 3 hγ
      simpa [Gamma0_mem] using hneg

end ArtinMatthews
