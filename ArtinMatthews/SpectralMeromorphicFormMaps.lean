module

public import ArtinMatthews.SpectralCompactPencilMeromorphic
public import ArtinMatthews.SpectralEisensteinContinuation


set_option backward.privateInPublic true
@[expose] public section

/-! Actual Banach-valued meromorphic operations used by the compact
truncated-form resolvent and its holomorphic forcing. -/
noncomputable section
namespace ArtinMatthews

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem spectralMeromorphicAt_comp_clm (A : E →L[ℂ] F) {f : ℂ → E} {z : ℂ}
    (hf : MeromorphicAt f z) : MeromorphicAt (fun w => A (f w)) z := by
  obtain ⟨n,hn⟩ := hf
  refine ⟨n,?_⟩
  simpa only [Function.comp_def,map_smul] using (A.analyticAt _).comp hn

theorem spectralMeromorphicAt_clmApply (A : ℂ → E →L[ℂ] F) (u : ℂ → E) (z : ℂ)
    (hA : MeromorphicAt A z) (hu : AnalyticAt ℂ u z) :
    MeromorphicAt (fun w => A w (u w)) z := by
  obtain ⟨n,hn⟩ := hA
  refine ⟨n,?_⟩
  simpa only [smul_apply] using
    spectralAnalytic_clmApply (fun w => (w-z)^n • A w) u z hn hu

def spectralOperatorSandwichLinear (J : E →L[ℂ] F) (K : F →L[ℂ] E) :
    (E →L[ℂ] E) →L[ℂ] (F →L[ℂ] F) :=
  (ContinuousLinearMap.compL ℂ F E F J).comp
    (ContinuousLinearMap.flip (E := E →L[ℂ] E) (F := F →L[ℂ] E) (G := F →L[ℂ] E)
      (σ₁₃ := RingHom.id ℂ) (σ₂₃ := RingHom.id ℂ) (ContinuousLinearMap.compL ℂ F E E) K)

theorem spectralOperatorSandwich_meromorphicAt (T : ℂ → E →L[ℂ] E) (z : ℂ)
    (hT : MeromorphicAt T z) (J : E →L[ℂ] F) (K : F →L[ℂ] E) :
    MeromorphicAt (fun w => J.comp ((T w).comp K)) z :=
  spectralMeromorphicAt_comp_clm (spectralOperatorSandwichLinear J K) hT

end
end ArtinMatthews
