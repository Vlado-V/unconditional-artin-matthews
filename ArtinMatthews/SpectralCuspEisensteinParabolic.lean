module

public import ArtinMatthews.SpectralCuspEisensteinDoubleCosets
public import ArtinMatthews.SpectralCuspEisensteinSeries


set_option backward.privateInPublic true
@[expose] public section

/-! The row index is the actual source parabolic quotient, and its weighted
terms are the genuine normalized source-cusp heights. -/
noncomputable section
open Matrix Set
open scoped MatrixGroups
namespace ArtinMatthews

theorem cuspEisenstein_same_row_iff_source_translation (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (M R : gamma0CuspCorrespondence N r a) :
    M.val 1=R.val 1 ↔ ∃ l : ℤ,
      R.val=integerTranslation ((gamma0CuspTrueWidth N a:ℤ)*l)*M.val := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := spectralModular_eq_translation_of_bottom_row_eq M.val R.val
      (congrFun h 0).symm (congrFun h 1).symm
    rw [← integerTranslation_eq_T_zpow] at hk
    have hp : a⁻¹*integerTranslation k*a ∈ CongruenceSubgroup.Gamma0 N := by
      have hh := (CongruenceSubgroup.Gamma0 N).mul_mem R.property
        ((CongruenceSubgroup.Gamma0 N).inv_mem M.property)
      have he : a⁻¹*integerTranslation k*a=
          (a⁻¹*R.val*r)*(a⁻¹*M.val*r)⁻¹ := by rw [hk]; group
      rw [he]
      exact hh
    obtain ⟨l,hl⟩ := (gamma0CuspTrueWidth_translation_iff N a k).mp hp
    exact ⟨l,hl ▸ hk⟩
  · rintro ⟨l,hl⟩
    rw [hl]
    funext j
    change M.val 1 j=∑ i : Fin 2,
      (integerTranslation ((gamma0CuspTrueWidth N a:ℤ)*l)) 1 i*M.val i j
    simp [integerTranslation,Fin.sum_univ_two]

def cuspEisensteinSourceRow (N : ℕ) (a : SL(2,ℤ))
    (γ : CongruenceSubgroup.Gamma0 N) : Gamma0CuspEisensteinRows N 1 a :=
  ⟨(a*γ.val) 1,by
    have hm : a*γ.val ∈ gamma0CuspCorrespondence N 1 a := by
      change a⁻¹*(a*γ.val)*1 ∈ CongruenceSubgroup.Gamma0 N
      simpa only [inv_mul_cancel_left,mul_one] using γ.property
    exact ⟨⟨a*γ.val,hm⟩,rfl⟩⟩

theorem cuspEisensteinSourceRow_surjective (N : ℕ) (a : SL(2,ℤ)) :
    Function.Surjective (cuspEisensteinSourceRow N a) := by
  intro v
  let M := gamma0CuspEisensteinRowRepresentative N 1 a v
  have hm : a⁻¹*M.val ∈ CongruenceSubgroup.Gamma0 N := by
    simpa only [gamma0CuspCorrespondence,mem_ofPred_eq,mul_one] using M.property
  let γ : CongruenceSubgroup.Gamma0 N := ⟨a⁻¹*M.val,hm⟩
  refine ⟨γ,?_⟩
  apply Subtype.ext
  change (a*(a⁻¹*M.val)) 1=v.val
  rw [mul_inv_cancel_left]
  exact gamma0CuspEisensteinRowRepresentative_spec N 1 a v

theorem cuspWidthDilation_im_inv_smul (w : ℝ) (hw : 0 < w) (z : UpperHalfPlane) :
    ((cuspWidthDilation w hw)⁻¹ • z).im=z.im/w := by
  have h := cuspWidthDilation_im_smul w hw ((cuspWidthDilation w hw)⁻¹ • z)
  rw [smul_inv_smul] at h
  apply (eq_div_iff hw.ne').mpr
  rw [mul_comm]
  exact h.symm

theorem cuspEisensteinSourceRow_normalized_term (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (γ : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    (gamma0CuspTrueWidth N a:ℂ)^(-s)*
      cuspEisensteinRowTerm N 1 a s (cuspEisensteinSourceRow N a γ) z=
      ((((gamma0TrueCuspScaling N a)⁻¹*atkinRealMap γ.val) • z).im:ℂ)^s := by
  have he : (gamma0TrueCuspScaling N a)⁻¹*atkinRealMap γ.val=
      (cuspWidthDilation (gamma0CuspTrueWidth N a:ℝ)
        (by exact_mod_cast gamma0CuspTrueWidth_pos N a))⁻¹*atkinRealMap (a*γ.val) := by
    unfold gamma0TrueCuspScaling
    rw [_root_.mul_inv_rev,inv_inv,map_mul]
    group
  rw [he,mul_smul,atkinRealMap_smul,cuspWidthDilation_im_inv_smul,
    Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (UpperHalfPlane.im_pos _).le
      (by positivity)]
  rw [cuspEisensteinRowTerm,cuspEisensteinRowHeight_of_row N 1 a _ (a*γ.val) rfl]
  rw [Complex.cpow_neg,div_eq_mul_inv]
  simp only [Complex.ofReal_natCast]
  ring

end ArtinMatthews
