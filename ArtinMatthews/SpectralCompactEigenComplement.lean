module

public import ArtinMatthews.SpectralCompactFormExceptional


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine invariant orthogonal complement of one eigenspace of a
compact symmetric operator. Its complementary pencil is invertible at the
chosen eigenparameter by the proved compact Fredholm alternative. -/
noncomputable section
open scoped InnerProductSpace
namespace ArtinMatthews

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

abbrev SpectralCompactEigenspace (T : V →L[ℂ] V) (μ : ℂ) : Submodule ℂ V :=
  Module.End.eigenspace T.toLinearMap μ

abbrev SpectralCompactEigenComplement (T : V →L[ℂ] V) (μ : ℂ) : Submodule ℂ V :=
  (SpectralCompactEigenspace T μ)ᗮ

local instance spectralCompactEigenComplement_complete (T : V →L[ℂ] V) (μ : ℂ) :
    CompleteSpace (SpectralCompactEigenComplement T μ) :=
  (Submodule.isClosed_orthogonal _).isComplete.completeSpace_coe

omit [CompleteSpace V] in
theorem spectralCompactEigenComplement_invariant (T : V →L[ℂ] V)
    (hTs : T.toLinearMap.IsSymmetric) (μ : ℂ) (u : SpectralCompactEigenComplement T μ) :
    T u.val ∈ SpectralCompactEigenComplement T μ := by
  apply ((SpectralCompactEigenspace T μ).mem_orthogonal _).mpr
  intro y hy
  have he : T y=μ • y := Module.End.mem_eigenspace_iff.mp hy
  have hz := ((SpectralCompactEigenspace T μ).mem_orthogonal _).mp u.property y hy
  calc
    inner ℂ y (T u.val)=inner ℂ (T y) u.val := (hTs y u.val).symm
    _=0 := by rw [he,inner_smul_left,hz,mul_zero]

def spectralCompactEigenComplementCompression (T : V →L[ℂ] V) (μ : ℂ) :
    SpectralCompactEigenComplement T μ →L[ℂ] SpectralCompactEigenComplement T μ :=
  (SpectralCompactEigenComplement T μ).orthogonalProjectionOnto.comp
    (T.comp (SpectralCompactEigenComplement T μ).subtypeL)

theorem spectralCompactEigenComplementCompression_val (T : V →L[ℂ] V)
    (hTs : T.toLinearMap.IsSymmetric) (μ : ℂ) (u : SpectralCompactEigenComplement T μ) :
    (spectralCompactEigenComplementCompression T μ u).val=T u.val := by
  let W := SpectralCompactEigenComplement T μ
  let v : W := ⟨T u.val,spectralCompactEigenComplement_invariant T hTs μ u⟩
  exact congrArg Subtype.val (W.orthogonalProjectionOnto_mem_subspace_eq_self v)

theorem spectralCompactEigenComplementCompression_compact (T : V →L[ℂ] V)
    (hT : IsCompactOperator T) (μ : ℂ) : IsCompactOperator (spectralCompactEigenComplementCompression T μ) :=
  (hT.comp_clm (SpectralCompactEigenComplement T μ).subtypeL).clm_comp
    (SpectralCompactEigenComplement T μ).orthogonalProjectionOnto

theorem spectralCompactEigenComplementPencil_isUnit (T : V →L[ℂ] V)
    (hT : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric) (z : ℂ) (hz : z+1≠0) :
    IsUnit (spectralCompactFormPencil (spectralCompactEigenComplementCompression T ((z+1)⁻¹)) z) := by
  let μ : ℂ := (z+1)⁻¹
  let W := SpectralCompactEigenComplement T μ
  apply (spectralCompactFormPencil_isUnit_iff _ (spectralCompactEigenComplementCompression_compact T hT μ) z).mpr
  intro u hu
  have hv := congrArg (fun v : W => v.val) hu
  change u.val-(z+1) • (spectralCompactEigenComplementCompression T μ u).val=0 at hv
  rw [spectralCompactEigenComplementCompression_val T hTs] at hv
  have he : T u.val=μ • u.val := calc
    _=μ • ((z+1) • T u.val) := by rw [smul_smul,show μ*(z+1)=1 from inv_mul_cancel₀ hz,one_smul]
    _=_ := congrArg (fun x : V => μ • x) (sub_eq_zero.mp hv).symm
  have hm : u.val ∈ SpectralCompactEigenspace T μ := Module.End.mem_eigenspace_iff.mpr he
  have horth := ((SpectralCompactEigenspace T μ).mem_orthogonal _).mp u.property u.val hm
  exact Subtype.ext (inner_self_eq_zero.mp horth)

end
end ArtinMatthews
