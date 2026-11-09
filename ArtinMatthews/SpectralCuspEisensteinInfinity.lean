module

public import ArtinMatthews.SpectralCuspEisensteinConstantTerm
public import ArtinMatthews.SpectralGamma0EisensteinScatteringEuler


set_option backward.privateInPublic true
@[expose] public section

/-! Literal calibration to the frozen infinity Eisenstein family, its true
period one, and its proved Euler scattering coefficient. -/
noncomputable section
open Matrix Set MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0CuspTrueWidth_identity (N : ℕ) [NeZero N] :
    gamma0CuspTrueWidth N (1:SL(2,ℤ))=1 := by
  apply Nat.le_antisymm
  · apply gamma0CuspTrueWidth_minimal N 1 1 (by norm_num)
    simp
  · exact gamma0CuspTrueWidth_pos N 1

def cuspEisensteinInfinityRowsEquiv (N : ℕ) :
    Gamma0EisensteinRows N ≃ Gamma0CuspEisensteinRows N 1 1 where
  toFun v := ⟨v.val,by
    let g := gamma0EisensteinRowRepresentative N v
    have hg : g.val ∈ gamma0CuspCorrespondence N 1 1 := by
      simpa only [gamma0CuspCorrespondence,mem_ofPred_eq,inv_one,one_mul,mul_one] using g.property
    exact ⟨⟨g.val,hg⟩,gamma0EisensteinRowRepresentative_spec N v⟩⟩
  invFun v := ⟨v.val,by
    let M := gamma0CuspEisensteinRowRepresentative N 1 1 v
    have hm : M.val ∈ CongruenceSubgroup.Gamma0 N := by
      simpa only [gamma0CuspCorrespondence,mem_ofPred_eq,inv_one,one_mul,mul_one] using M.property
    exact ⟨⟨M.val,hm⟩,gamma0CuspEisensteinRowRepresentative_spec N 1 1 v⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem gamma0CuspEisenstein_identity_eq (N : ℕ) [NeZero N] (s : ℂ) (z : UpperHalfPlane) :
    gamma0CuspEisenstein N 1 s z=gamma0Eisenstein N s z := by
  unfold gamma0CuspEisenstein
  rw [gamma0CuspTrueWidth_identity]
  simp only [Nat.cast_one,Complex.one_cpow,one_mul]
  unfold cuspEisensteinRowSum gamma0Eisenstein
  congr 1
  rw [← (cuspEisensteinInfinityRowsEquiv N).tsum_eq
    (fun v : Gamma0CuspEisensteinRows N 1 1 => cuspEisensteinRowTerm N 1 1 s v z)]
  apply tsum_congr
  intro v
  rw [cuspEisensteinRowTerm,cuspEisensteinRowHeight_row,
    gamma0EisensteinSummand,gamma0EisensteinHeight_row]
  rfl

theorem gamma0TrueCuspScaling_identity (N : ℕ) [NeZero N] :
    gamma0TrueCuspScaling N (1:SL(2,ℤ))=1 := by
  unfold gamma0TrueCuspScaling
  simp only [gamma0CuspTrueWidth_identity,map_one,inv_one,one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cuspWidthDilation]

theorem gamma0EisensteinCuspsEquivalent_refl (N : ℕ) (a : SL(2,ℤ)) :
    gamma0EisensteinCuspsEquivalent N a a := by
  apply (gamma0EisensteinCuspsEquivalent_iff N a a).mpr
  refine ⟨⟨1,?_⟩,by simp⟩
  change a⁻¹*1*a ∈ CongruenceSubgroup.Gamma0 N
  simp

theorem gamma0CuspEisensteinIndicator_refl (N : ℕ) (a : SL(2,ℤ)) :
    gamma0CuspEisensteinIndicator N a a=1 := by
  simp [gamma0CuspEisensteinIndicator,gamma0EisensteinCuspsEquivalent_refl]

theorem gamma0CuspScattering_identity_eq (N : ℕ) [NeZero N] (s : ℂ) (hs : 1 < s.re) :
    gamma0CuspScattering N 1 1 s=gamma0EisensteinScatteringInfinity N s := by
  have h := gamma0CuspEisenstein_all_cusp_constant_term N 1 1 s hs 1 (by norm_num)
  simp only [gamma0TrueCuspScaling_identity,one_smul,gamma0CuspEisenstein_identity_eq,
    gamma0CuspEisensteinIndicator_refl,Complex.ofReal_one,Complex.one_cpow,mul_one,one_mul] at h
  have hInf := gamma0Eisenstein_infinity_constant_term N s hs 1 (by norm_num)
  change (∫ x in (0:ℝ)..1, gamma0Eisenstein N s (gamma0EisensteinHorizontalPoint 1 (by norm_num) x))=_ at hInf
  simp only [Complex.ofReal_one,Complex.one_cpow,one_mul] at hInf
  rw [hInf] at h
  exact (add_left_cancel h).symm

end ArtinMatthews
