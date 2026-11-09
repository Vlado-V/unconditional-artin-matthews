module

public import ArtinMatthews.AtkinLehnerArithmetic


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Gamma0 normalizer at an exact-divisor cusp. -/
namespace ArtinMatthews

open Matrix CongruenceSubgroup

abbrev atkinRealMap : Matrix.SpecialLinearGroup (Fin 2) ℤ →*
    Matrix.SpecialLinearGroup (Fin 2) ℝ := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)

def atkinGammaSL (r s : ℕ) (A B C D : ℤ)
    (hdet : A*D-(r : ℤ)*(s : ℤ)*B*C = 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨atkinGammaMatrix r s A B C D,by rw [atkinGammaMatrix_det]; exact hdet⟩

def atkinGammaForwardSL (r s : ℕ) (a b A B C D : ℤ)
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (hdet : A*D-(r : ℤ)*(s : ℤ)*B*C = 1) :
    Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨atkinGammaForward r s a b A B C D,by rw [atkinGammaForward_det,hab,hdet]; norm_num⟩

def atkinGammaBackwardSL (r s : ℕ) (a b A B C D : ℤ)
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (hdet : A*D-(r : ℤ)*(s : ℤ)*B*C = 1) :
    Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨atkinGammaBackward r s a b A B C D,by rw [atkinGammaBackward_det,hab,hdet]; norm_num⟩

theorem atkinGammaSL_mem (r s : ℕ) (A B C D : ℤ)
    (hdet : A*D-(r : ℤ)*(s : ℤ)*B*C = 1) :
    atkinGammaSL r s A B C D hdet ∈ Gamma0 (r*s) := by
  rw [Gamma0_mem,ZMod.intCast_zmod_eq_zero_iff_dvd]
  change ((r*s : ℕ) : ℤ) ∣ (r : ℤ)*(s : ℤ)*C
  exact ⟨C,by push_cast; rfl⟩

theorem atkinGammaForwardSL_mem (r s : ℕ) (a b A B C D : ℤ)
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (hdet : A*D-(r : ℤ)*(s : ℤ)*B*C = 1) :
    atkinGammaForwardSL r s a b A B C D hab hdet ∈ Gamma0 (r*s) := by
  rw [Gamma0_mem,ZMod.intCast_zmod_eq_zero_iff_dvd]
  change ((r*s : ℕ) : ℤ) ∣ (r : ℤ)*(s : ℤ)*(-A+(r : ℤ)*C-(s : ℤ)*B+D)
  exact ⟨-A+(r : ℤ)*C-(s : ℤ)*B+D,by push_cast; rfl⟩

theorem atkinGammaBackwardSL_mem (r s : ℕ) (a b A B C D : ℤ)
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (hdet : A*D-(r : ℤ)*(s : ℤ)*B*C = 1) :
    atkinGammaBackwardSL r s a b A B C D hab hdet ∈ Gamma0 (r*s) := by
  rw [Gamma0_mem,ZMod.intCast_zmod_eq_zero_iff_dvd]
  change ((r*s : ℕ) : ℤ) ∣ (r : ℤ)*(s : ℤ)*(a*A+(r : ℤ)*a^2*C-(s : ℤ)*B-a*D)
  exact ⟨a*A+(r : ℤ)*a^2*C-(s : ℤ)*B-a*D,by push_cast; rfl⟩

/-- Every actual Gamma0 matrix has the literal integer parameterization used
in the polynomial conjugation identities. -/
theorem atkinGammaSL_parameterization {r s : ℕ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ ∈ Gamma0 (r*s)) :
    ∃ (A B C D : ℤ) (hdet : A*D-(r : ℤ)*(s : ℤ)*B*C = 1),
      atkinGammaSL r s A B C D hdet = γ := by
  have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) (r*s)).mp (Gamma0_mem.mp hγ)
  obtain ⟨C,hC⟩ := hdiv
  push_cast at hC
  have hdet : γ 0 0 * γ 1 1-(r : ℤ)*(s : ℤ)*(γ 0 1)*C = 1 := by
    have hh := γ.prop
    rw [Matrix.det_fin_two] at hh
    rw [hC] at hh
    nlinarith
  refine ⟨γ 0 0,γ 0 1,C,γ 1 1,hdet,?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [atkinGammaSL,atkinGammaMatrix,hC]

set_option backward.isDefEq.respectTransparency false in
theorem atkinScaling_conjugate_forward {r s : ℕ} (hr : 0 < r)
    (a b A B C D : ℤ) (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (hdet : A*D-(r : ℤ)*(s : ℤ)*B*C = 1) :
    (atkinScaling hr hab)⁻¹ * atkinRealMap (atkinGammaSL r s A B C D hdet) *
        atkinScaling hr hab =
      atkinRealMap (atkinGammaForwardSL r s a b A B C D hab hdet) := by
  have hm : atkinRealMap (atkinGammaSL r s A B C D hdet) * atkinScaling hr hab =
      atkinScaling hr hab * atkinRealMap (atkinGammaForwardSL r s a b A B C D hab hdet) := by
    apply Subtype.ext
    exact (atkinScalingMatrix_forward hab A B C D).symm
  rw [mul_assoc,hm,← mul_assoc,inv_mul_cancel,one_mul]

set_option backward.isDefEq.respectTransparency false in
theorem atkinScaling_conjugate_backward {r s : ℕ} (hr : 0 < r)
    (a b A B C D : ℤ) (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (hdet : A*D-(r : ℤ)*(s : ℤ)*B*C = 1) :
    atkinScaling hr hab * atkinRealMap (atkinGammaSL r s A B C D hdet) *
        (atkinScaling hr hab)⁻¹ =
      atkinRealMap (atkinGammaBackwardSL r s a b A B C D hab hdet) := by
  have hm : atkinScaling hr hab * atkinRealMap (atkinGammaSL r s A B C D hdet) =
      atkinRealMap (atkinGammaBackwardSL r s a b A B C D hab hdet) * atkinScaling hr hab := by
    apply Subtype.ext
    exact (atkinScalingMatrix_backward hab A B C D).symm
  rw [hm,mul_assoc,mul_inv_cancel,mul_one]

/-- The actual forward conjugation stays inside the mapped congruence group. -/
theorem atkinScaling_normalizes_forward {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ ∈ Gamma0 (r*s)) :
    ∃ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Gamma0 (r*s) ∧
      (atkinScaling hr hab)⁻¹ * atkinRealMap γ * atkinScaling hr hab = atkinRealMap δ := by
  obtain ⟨A,B,C,D,hdet,rfl⟩ := atkinGammaSL_parameterization γ hγ
  exact ⟨atkinGammaForwardSL r s a b A B C D hab hdet,
    atkinGammaForwardSL_mem r s a b A B C D hab hdet,
    atkinScaling_conjugate_forward hr a b A B C D hab hdet⟩

/-- The reverse conjugation also stays in the group, proving equality rather
than a one-sided arithmetic inclusion. -/
theorem atkinScaling_normalizes_backward {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ ∈ Gamma0 (r*s)) :
    ∃ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Gamma0 (r*s) ∧
      atkinScaling hr hab * atkinRealMap γ * (atkinScaling hr hab)⁻¹ = atkinRealMap δ := by
  obtain ⟨A,B,C,D,hdet,rfl⟩ := atkinGammaSL_parameterization γ hγ
  exact ⟨atkinGammaBackwardSL r s a b A B C D hab hdet,
    atkinGammaBackwardSL_mem r s a b A B C D hab hdet,
    atkinScaling_conjugate_backward hr a b A B C D hab hdet⟩

end ArtinMatthews
