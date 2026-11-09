module

public import ArtinMatthews.SpectralCuspEisensteinParabolic


set_option backward.privateInPublic true
@[expose] public section

/-! Actual enumeration of the full congruence group by source rows and their
true parabolic translation parameter. Both central signs remain in the rows. -/
noncomputable section
open Matrix Set
open scoped MatrixGroups
namespace ArtinMatthews

theorem integerTranslation_bottom_row (k : ℤ) (M : SL(2,ℤ)) :
    (integerTranslation k*M) 1=M 1 := by
  funext j
  change (∑ i : Fin 2, (integerTranslation k) 1 i*M i j)=M 1 j
  simp [integerTranslation,Fin.sum_univ_two]

def cuspEisensteinParabolicEnumerate (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (p : Gamma0CuspEisensteinRows N 1 a × ℤ) : CongruenceSubgroup.Gamma0 N := by
  let M := gamma0CuspEisensteinRowRepresentative N 1 a p.1
  let T := integerTranslation ((gamma0CuspTrueWidth N a:ℤ)*p.2)
  have hT : a⁻¹*T*a ∈ CongruenceSubgroup.Gamma0 N :=
    (gamma0CuspTrueWidth_translation_iff N a _).mpr (dvd_mul_right _ _)
  have hM : a⁻¹*M.val ∈ CongruenceSubgroup.Gamma0 N := by
    simpa only [gamma0CuspCorrespondence,mem_ofPred_eq,mul_one] using M.property
  refine ⟨a⁻¹*T*M.val,?_⟩
  have h := (CongruenceSubgroup.Gamma0 N).mul_mem hT hM
  convert h using 1
  group

theorem cuspEisensteinParabolicEnumerate_matrix (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (p : Gamma0CuspEisensteinRows N 1 a × ℤ) :
    a*(cuspEisensteinParabolicEnumerate N a p).val=
      integerTranslation ((gamma0CuspTrueWidth N a:ℤ)*p.2)*
        (gamma0CuspEisensteinRowRepresentative N 1 a p.1).val := by
  change a*(a⁻¹*integerTranslation ((gamma0CuspTrueWidth N a:ℤ)*p.2)*
    (gamma0CuspEisensteinRowRepresentative N 1 a p.1).val)=_
  group

theorem cuspEisensteinParabolicEnumerate_row (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (p : Gamma0CuspEisensteinRows N 1 a × ℤ) :
    (a*(cuspEisensteinParabolicEnumerate N a p).val) 1=p.1.val := by
  rw [cuspEisensteinParabolicEnumerate_matrix,integerTranslation_bottom_row,
    gamma0CuspEisensteinRowRepresentative_spec]

theorem cuspEisensteinParabolicEnumerate_injective (N : ℕ) [NeZero N] (a : SL(2,ℤ)) :
    Function.Injective (cuspEisensteinParabolicEnumerate N a) := by
  rintro ⟨v,k⟩ ⟨w,l⟩ h
  have hv : v=w := by
    apply Subtype.ext
    have he := congrArg (fun γ : CongruenceSubgroup.Gamma0 N => (a*γ.val) 1) h
    simpa only [cuspEisensteinParabolicEnumerate_row] using he
  subst w
  have hm := congrArg (fun γ : CongruenceSubgroup.Gamma0 N => a*γ.val) h
  rw [cuspEisensteinParabolicEnumerate_matrix,cuspEisensteinParabolicEnumerate_matrix] at hm
  have ht := mul_right_cancel hm
  have hentry := congrArg (fun M : SL(2,ℤ) => M 0 1) ht
  change (gamma0CuspTrueWidth N a:ℤ)*k=(gamma0CuspTrueWidth N a:ℤ)*l at hentry
  have hkl := mul_left_cancel₀ (show (gamma0CuspTrueWidth N a:ℤ) ≠ 0 by
    exact_mod_cast (gamma0CuspTrueWidth_pos N a).ne') hentry
  exact Prod.ext rfl hkl

theorem cuspEisensteinParabolicEnumerate_surjective (N : ℕ) [NeZero N] (a : SL(2,ℤ)) :
    Function.Surjective (cuspEisensteinParabolicEnumerate N a) := by
  intro γ
  let v := cuspEisensteinSourceRow N a γ
  let M := gamma0CuspEisensteinRowRepresentative N 1 a v
  have hg : a*γ.val ∈ gamma0CuspCorrespondence N 1 a := by
    change a⁻¹*(a*γ.val)*1 ∈ CongruenceSubgroup.Gamma0 N
    simpa only [inv_mul_cancel_left,mul_one] using γ.property
  have hr : M.val 1=(a*γ.val) 1 := gamma0CuspEisensteinRowRepresentative_spec N 1 a v
  obtain ⟨l,hl⟩ := (cuspEisenstein_same_row_iff_source_translation N 1 a M ⟨a*γ.val,hg⟩).mp hr
  refine ⟨(v,l),?_⟩
  apply Subtype.ext
  apply mul_left_cancel (a := a)
  rw [cuspEisensteinParabolicEnumerate_matrix]
  exact hl.symm

def cuspEisensteinParabolicEquiv (N : ℕ) [NeZero N] (a : SL(2,ℤ)) :
    (Gamma0CuspEisensteinRows N 1 a × ℤ) ≃ CongruenceSubgroup.Gamma0 N :=
  Equiv.ofBijective _ ⟨cuspEisensteinParabolicEnumerate_injective N a,
    cuspEisensteinParabolicEnumerate_surjective N a⟩

end ArtinMatthews
