module

public import ArtinMatthews.SpectralCompactEigenSplitInverse
public import ArtinMatthews.SpectralGamma0AmbientResolventAnalytic
public import Mathlib.Analysis.Meromorphic.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Meromorphic inverse of the genuine compact symmetric form pencil. Near
a singular parameter its invariant complement is analytic and the actual
eigenspace projection has the literal scalar pole factor. -/
noncomputable section
open Set Filter Topology
open scoped InnerProductSpace
namespace ArtinMatthews

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

local instance spectralCompactPencilMeromorphic_space_complete (T : V →L[ℂ] V) (μ : ℂ) :
    CompleteSpace (SpectralCompactEigenspace T μ) :=
  (ContinuousLinearMap.isClosed_eigenspace T μ).isComplete.completeSpace_coe

local instance spectralCompactPencilMeromorphic_complement_complete (T : V →L[ℂ] V) (μ : ℂ) :
    CompleteSpace (SpectralCompactEigenComplement T μ) :=
  (Submodule.isClosed_orthogonal _).isComplete.completeSpace_coe

theorem spectralCompactEigenSplitInverse_meromorphicAt (T : V →L[ℂ] V) (μ z₀ : ℂ)
    (hW : IsUnit (spectralCompactFormPencil (spectralCompactEigenComplementCompression T μ) z₀)) :
    MeromorphicAt (spectralCompactEigenSplitInverse T μ) z₀ := by
  let S := SpectralCompactEigenspace T μ
  let W := SpectralCompactEigenComplement T μ
  let C := spectralCompactEigenComplementCompression T μ
  have hC : AnalyticAt ℂ (fun z => Ring.inverse (spectralCompactFormPencil C z)) z₀ :=
    spectralOperatorPencilInverse_analyticAt C z₀ hW
  have hB : AnalyticAt ℂ (fun z => W.subtypeL.comp
      ((Ring.inverse (spectralCompactFormPencil C z)).comp W.orthogonalProjectionOnto)) z₀ :=
    spectralOperatorSandwich_analyticAt _ hC W.subtypeL W.orthogonalProjectionOnto
  have hc : AnalyticAt ℂ (fun z : ℂ => 1-(z+1)*μ) z₀ :=
    analyticAt_const.sub ((analyticAt_id.add analyticAt_const).mul analyticAt_const)
  have hA : MeromorphicAt (fun z : ℂ => (1-(z+1)*μ)⁻¹ • S.starProjection) z₀ :=
    hc.meromorphicAt.inv.smul (MeromorphicAt.const S.starProjection z₀)
  exact hA.add hB.meromorphicAt

theorem spectralCompactFormPencil_inverse_eventually_split (T : V →L[ℂ] V)
    (hT : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric) (z₀ : ℂ) (hz₀ : z₀+1≠0) :
    spectralCompactEigenSplitInverse T ((z₀+1)⁻¹) =ᶠ[𝓝[≠] z₀]
      fun z => Ring.inverse (spectralCompactFormPencil T z) := by
  let μ : ℂ := (z₀+1)⁻¹
  let C := spectralCompactEigenComplementCompression T μ
  have hW : IsUnit (spectralCompactFormPencil C z₀) :=
    spectralCompactEigenComplementPencil_isUnit T hT hTs z₀ hz₀
  have hc : ContinuousAt (spectralCompactFormPencil C) z₀ :=
    (spectralOperatorPencil_analyticAt C z₀).continuousAt
  have hWnear : ∀ᶠ z in 𝓝[≠] z₀, IsUnit (spectralCompactFormPencil C z) :=
    nhdsWithin_le_nhds (hc (Units.isOpen.mem_nhds hW))
  have hPnear := spectralCompactFormPencil_eventually_isUnit_punctured T hT hTs z₀
  have hne : ∀ᶠ z in 𝓝[≠] z₀, z∈({z₀}:Set ℂ)ᶜ := self_mem_nhdsWithin
  filter_upwards [hWnear,hPnear,hne] with z hWz hPz hz
  have hz' : z≠z₀ := by simpa only [mem_compl_iff,mem_singleton_iff] using hz
  have h0 : (z₀+1)*μ=1 := mul_inv_cancel₀ hz₀
  have hd : 1-(z+1)*μ=(z₀-z)*μ := by linear_combination -h0
  have hden : 1-(z+1)*μ≠0 := hd ▸ mul_ne_zero (sub_ne_zero.mpr hz'.symm) (inv_ne_zero hz₀)
  exact spectralCompactEigenSplitInverse_eq_inverse T hTs μ z hden hWz hPz

theorem spectralCompactFormPencil_inverse_meromorphicAt (T : V →L[ℂ] V)
    (hT : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric) (z₀ : ℂ) :
    MeromorphicAt (fun z => Ring.inverse (spectralCompactFormPencil T z)) z₀ := by
  by_cases hP : IsUnit (spectralCompactFormPencil T z₀)
  · exact (spectralOperatorPencilInverse_analyticAt T z₀ hP).meromorphicAt
  · have hne : z₀+1≠0 := by
      intro hz
      apply hP
      rw [spectralCompactFormPencil,hz,zero_smul,sub_zero]
      exact isUnit_one
    exact (spectralCompactEigenSplitInverse_meromorphicAt T ((z₀+1)⁻¹) z₀
      (spectralCompactEigenComplementPencil_isUnit T hT hTs z₀ hne)).congr
        (spectralCompactFormPencil_inverse_eventually_split T hT hTs z₀ hne)

theorem spectralCompactFormPencil_inverse_meromorphic (T : V →L[ℂ] V)
    (hT : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric) :
    Meromorphic (fun z => Ring.inverse (spectralCompactFormPencil T z)) :=
  fun z => spectralCompactFormPencil_inverse_meromorphicAt T hT hTs z

end
end ArtinMatthews
