module

public import ArtinMatthews.SpectralCuspEisensteinResidueRows
public import ArtinMatthews.SpectralModularStripCountInjection


set_option backward.privateInPublic true
@[expose] public section

/-! The actual parabolic row residues are exactly the frozen true-width
positive-c double cosets. No multiplicity or source width is suppressed. -/
noncomputable section
open Matrix Set
open scoped MatrixGroups
namespace ArtinMatthews

def cuspEisensteinReducedMatrixRow (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (c : ℕ) [NeZero c] (M : gamma0TrueWidthReducedMatrix N r a c) :
    CuspEisensteinRowResidues N r a c := by
  have ht : ((M.val 1 1).toNat:ℤ)=M.val 1 1 := Int.toNat_of_nonneg M.property.2.2.2.2.1
  refine ⟨⟨(M.val 1 1).toNat,?_⟩,?_⟩
  · exact_mod_cast (show ((M.val 1 1).toNat:ℤ)<((gamma0CuspTrueWidth N r*c:ℕ):ℤ) by
      rw [ht,Nat.cast_mul]
      exact M.property.2.2.2.2.2)
  · refine ⟨⟨M.val,M.property.1⟩,?_⟩
    funext j
    fin_cases j
    · exact M.property.2.1
    · exact ht.symm

theorem cuspEisensteinReducedMatrixRow_int (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (c : ℕ) [NeZero c] (M : gamma0TrueWidthReducedMatrix N r a c) :
    ((cuspEisensteinReducedMatrixRow N r a c M).val.val:ℤ)=M.val 1 1 :=
  Int.toNat_of_nonneg M.property.2.2.2.2.1

theorem cuspEisensteinReducedMatrixRow_injective (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (c : ℕ) [NeZero c] : Function.Injective (cuspEisensteinReducedMatrixRow N r a c) := by
  intro M R h
  have hd := congrArg (fun d : CuspEisensteinRowResidues N r a c => (d.val.val:ℤ)) h
  rw [cuspEisensteinReducedMatrixRow_int,cuspEisensteinReducedMatrixRow_int] at hd
  obtain ⟨k,hk⟩ := spectralModular_eq_translation_of_bottom_row_eq M.val R.val
    (R.property.2.1.trans M.property.2.1.symm) hd.symm
  rw [← integerTranslation_eq_T_zpow] at hk
  have hp : a⁻¹*integerTranslation k*a ∈ CongruenceSubgroup.Gamma0 N := by
    have hh := (CongruenceSubgroup.Gamma0 N).mul_mem R.property.1
      ((CongruenceSubgroup.Gamma0 N).inv_mem M.property.1)
    have he : a⁻¹*integerTranslation k*a=
        (a⁻¹*R.val*r)*(a⁻¹*M.val*r)⁻¹ := by rw [hk]; group
    rw [he]
    exact hh
  obtain ⟨l,hl⟩ := (gamma0CuspTrueWidth_translation_iff N a k).mp hp
  have h0 : integerTranslation 0=(1:SL(2,ℤ)) := by simp [integerTranslation_eq_T_zpow]
  have hA := (integerTranslation_entries k 0 M.val).1
  simp only [h0,mul_one] at hA
  have heA : M.val 0 0+((gamma0CuspTrueWidth N a:ℤ)*c)*l=R.val 0 0+
      ((gamma0CuspTrueWidth N a:ℤ)*c)*0 := by
    rw [hk,hA,M.property.2.1,hl]
    ring
  have hL : 0 < (gamma0CuspTrueWidth N a:ℤ)*c := mul_pos
    (by exact_mod_cast gamma0CuspTrueWidth_pos N a) (by exact_mod_cast NeZero.pos c)
  have hAR := (integer_interval_translate_unique hL
    ⟨M.property.2.2.1,M.property.2.2.2.1⟩ ⟨R.property.2.2.1,R.property.2.2.2.1⟩ heA).1
  apply Subtype.ext
  exact specialLinear_eq_of_diagonal_lower (by exact_mod_cast NeZero.ne c)
    M.val R.val M.property.2.1 R.property.2.1 hAR hd

theorem cuspEisensteinReducedMatrixRow_surjective (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (c : ℕ) [NeZero c] : Function.Surjective (cuspEisensteinReducedMatrixRow N r a c) := by
  intro b
  obtain ⟨M,hM⟩ := b.property
  have hc : M.val 1 0=c := congrFun hM 0
  have hd : M.val 1 1=(b.val.val:ℤ) := congrFun hM 1
  let F : gamma0CuspMatrixFibre N r a c := ⟨M.val,M.property,hc⟩
  obtain ⟨⟨R,l,k⟩,he⟩ := (gamma0TrueWidthDoubleCosetEquiv N r a c).surjective F
  have hD := congrArg (fun M : gamma0CuspMatrixFibre N r a c => M.val 1 1) he
  change (integerTranslation ((gamma0CuspTrueWidth N a:ℤ)*l)*R.val*
    integerTranslation ((gamma0CuspTrueWidth N r:ℤ)*k) : SL(2,ℤ)) 1 1=M.val 1 1 at hD
  rw [(integerTranslation_entries _ _ _).2.2,R.property.2.1,hd] at hD
  have hL : 0 < (gamma0CuspTrueWidth N r:ℤ)*c := mul_pos
    (by exact_mod_cast gamma0CuspTrueWidth_pos N r) (by exact_mod_cast NeZero.pos c)
  have hb : (0:ℤ) ≤ b.val.val ∧ (b.val.val:ℤ)<(gamma0CuspTrueWidth N r:ℤ)*c :=
    ⟨by positivity,by exact_mod_cast b.val.isLt⟩
  have hRd := (integer_interval_translate_unique hL
    ⟨R.property.2.2.2.2.1,R.property.2.2.2.2.2⟩ hb
    (show R.val 1 1+((gamma0CuspTrueWidth N r:ℤ)*c)*k=(b.val.val:ℤ)+
      ((gamma0CuspTrueWidth N r:ℤ)*c)*0 by nlinarith [hD])).1
  refine ⟨R,?_⟩
  apply Subtype.ext
  apply Fin.ext
  apply Int.ofNat_inj.mp
  exact (cuspEisensteinReducedMatrixRow_int N r a c R).trans hRd

def cuspEisensteinReducedMatrixRowEquiv (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (c : ℕ) [NeZero c] : gamma0TrueWidthReducedMatrix N r a c ≃ CuspEisensteinRowResidues N r a c :=
  Equiv.ofBijective _ ⟨cuspEisensteinReducedMatrixRow_injective N r a c,
    cuspEisensteinReducedMatrixRow_surjective N r a c⟩

end ArtinMatthews
