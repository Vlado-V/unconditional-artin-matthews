module

public import ArtinMatthews.CubicThetaUnweightedSlash
public import ArtinMatthews.CubicThetaGammaGeneratorsClosure
public import ArtinMatthews.ShiftedVoronoiCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! The exact level-three transformation law of the unweighted Eisenstein
theta, derived from Poisson inversion and the proved two-generator theorem. -/
noncomputable section
namespace ArtinMatthews

open Complex UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups

/-- The unweighted theta is invariant under the full Γ₁(3), with generation
proved by integer Euclidean descent. -/
theorem eisensteinHolomorphicTheta_slash_Gamma1_three (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma1 3) :
    eisensteinHolomorphicTheta ∣[(1 : ℤ)] γ = eisensteinHolomorphicTheta := by
  rw [Gamma1_three_eq_closure_T_U3] at hγ
  apply Subgroup.closure_induction
    (p := fun g _ => eisensteinHolomorphicTheta ∣[(1 : ℤ)] g = eisensteinHolomorphicTheta)
    ?_ ?_ ?_ ?_ hγ
  · intro g hg
    rcases hg with rfl | rfl
    · exact eisensteinHolomorphicTheta_slash_T
    · have he : cubicThetaU3 = eisensteinLowerUnipotent 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> norm_num [cubicThetaU3, eisensteinLowerUnipotent]
      rw [he]
      exact eisensteinHolomorphicTheta_slash_lowerUnipotent 1
  · exact SlashAction.slash_one _ _
  · intro a b _ _ ha hb
    rw [SlashAction.slash_mul, ha, hb]
  · intro a _ ha
    rw [← ha, ← SlashAction.slash_mul]
    simp [ha]

/-- The corresponding classical weight-one identity. -/
theorem eisensteinHolomorphicTheta_Gamma1_three (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma1 3) (τ : ℍ) :
    eisensteinHolomorphicTheta (γ • τ) =
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) * eisensteinHolomorphicTheta τ := by
  have h := congrFun (eisensteinHolomorphicTheta_slash_Gamma1_three γ hγ) τ
  rw [SL_slash_apply] at h
  have hd : UpperHalfPlane.denom γ τ = (γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ) :=
    ModularGroup.denom_apply γ τ
  have hn := UpperHalfPlane.denom_ne_zero γ τ
  have hdiv : eisensteinHolomorphicTheta (γ • τ) / UpperHalfPlane.denom γ τ =
      eisensteinHolomorphicTheta τ := by
    simpa only [zpow_neg_one, div_eq_mul_inv] using h
  have he := (div_eq_iff hn).mp hdiv
  rw [hd, mul_comm] at he
  exact he

/-- The actual nebentypus on Γ₀(3) is χ₋₃(d), exactly the one used by the
signed Voronoi formula. -/
theorem eisensteinHolomorphicTheta_Gamma0_three (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma0 3) (τ : ℍ) :
    eisensteinHolomorphicTheta (γ • τ) =
      cubicThetaNebentypus (γ 1 1) *
        ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) * eisensteinHolomorphicTheta τ := by
  have hc : (3 : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  rcases cubicThetaKernel_signed_membership 3 (dvd_refl 3) γ hc with
    ⟨hpos, hψ⟩ | ⟨hneg, hψ⟩
  · rw [hψ, one_mul]
    exact eisensteinHolomorphicTheta_Gamma1_three γ hpos.2 τ
  · rw [hψ]
    have h := eisensteinHolomorphicTheta_Gamma1_three (-γ) hneg.2 τ
    have hcneg : (-γ) 1 0 = -(γ 1 0) := rfl
    have hdneg : (-γ) 1 1 = -(γ 1 1) := rfl
    simp only [ModularGroup.SL_neg_smul, hcneg, hdneg, Int.cast_neg] at h
    rw [h]
    ring

end ArtinMatthews
