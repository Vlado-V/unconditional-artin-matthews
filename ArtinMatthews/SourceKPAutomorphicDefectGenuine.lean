module

public import ArtinMatthews.SourceKPAutomorphicDefectL2
public import ArtinMatthews.SourceKPAdelicCutoffDefectGenuine
public import ArtinMatthews.SourceKPCompactGenuineL2


set_option backward.privateInPublic true
@[expose] public section

/-! The same literal compact defect is an entire family in the actual
genuine automorphic Hilbert space. -/

namespace ArtinMatthews
open NumberField MeasureTheory Filter
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAutomorphicCompactCutoffDefect_center {T : ℝ} (hT : 0 < T) (s : ℂ)
    (z : rootsOfUnity 3 K) (x : SourceKPAutomorphicCompactLevel K hζ) :
    sourceKPAutomorphicCompactCutoffDefect K hζ hT s (z • x) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ)*sourceKPAutomorphicCompactCutoffDefect K hζ hT s x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    obtain ⟨q,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
    change sourceKPAutomorphicCompactCutoffDefect K hζ hT s
      (z • sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q)) =
        (sourceKPAdelicCentralComplex K hζ z : ℂ)*sourceKPAutomorphicCompactCutoffDefect K hζ hT s
          (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q))
    rw [sourceKPCubicCenter_compact_mk,sourceKPCubicCenter_automorphic_mk,
      sourceKPAutomorphicCompactCutoffDefect_adelic,sourceKPAutomorphicCompactCutoffDefect_adelic]
    exact sourceKPAdelicCutoffCasimirDefect_center K hζ T s z q

theorem sourceKPAutomorphicDefectL2_mem_genuine {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    sourceKPAutomorphicDefectL2 K hζ hT s ∈
      sourceKPCompactGenuineL2Subspace K hζ (sourceKPArchHaar K hζ) := by
  apply (sourceKPCompactGenuineL2Subspace_mem_ae K hζ (sourceKPArchHaar K hζ) _).mpr
  intro z
  have hAE := sourceKPAutomorphicDefectL2_ae K hζ hT s
  have hZ := (sourceKPAutomorphicCompactMeasure_center_preserving K hζ z
    (sourceKPArchHaar K hζ)).quasiMeasurePreserving.ae_eq_comp hAE
  filter_upwards [hAE,hZ] with x hx hzx
  calc
    sourceKPAutomorphicDefectL2 K hζ hT s (z • x) =
        sourceKPAutomorphicCompactCutoffDefect K hζ (lt_of_lt_of_le zero_lt_one hT) s (z • x) := hzx
    _ = (sourceKPAdelicCentralComplex K hζ z : ℂ)*
        sourceKPAutomorphicCompactCutoffDefect K hζ (lt_of_lt_of_le zero_lt_one hT) s x :=
      sourceKPAutomorphicCompactCutoffDefect_center K hζ (lt_of_lt_of_le zero_lt_one hT) s z x
    _ = _ := congrArg (fun w => (sourceKPAdelicCentralComplex K hζ z : ℂ)*w) hx.symm

def sourceKPAutomorphicGenuineDefectL2 {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    SourceKPGenuineAutomorphicL2 K hζ :=
  (sourceKPCompactGenuineL2Subspace K hζ (sourceKPArchHaar K hζ)).orthogonalProjectionOnto
    (sourceKPAutomorphicDefectL2 K hζ hT s)

theorem sourceKPAutomorphicGenuineDefectL2_coe {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    (sourceKPAutomorphicGenuineDefectL2 K hζ hT s :
      SourceKPAutomorphicL2 K hζ (sourceKPArchHaar K hζ)) = sourceKPAutomorphicDefectL2 K hζ hT s :=
  Submodule.starProjection_mem_subspace_eq_self
    (⟨sourceKPAutomorphicDefectL2 K hζ hT s,sourceKPAutomorphicDefectL2_mem_genuine K hζ hT s⟩ :
      SourceKPGenuineAutomorphicL2 K hζ)

theorem sourceKPAutomorphicGenuineDefectL2_entire {T : ℝ} (hT : 1 ≤ T) :
    Differentiable ℂ (sourceKPAutomorphicGenuineDefectL2 K hζ hT) :=
  (sourceKPCompactGenuineL2Subspace K hζ (sourceKPArchHaar K hζ)).orthogonalProjectionOnto.differentiable.comp
    (sourceKPAutomorphicDefectL2_entire K hζ hT)

theorem sourceKPAutomorphicGenuineDefectL2_analyticAt {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    AnalyticAt ℂ (sourceKPAutomorphicGenuineDefectL2 K hζ hT) s :=
  (sourceKPAutomorphicGenuineDefectL2_entire K hζ hT).analyticAt s

end
end ArtinMatthews
