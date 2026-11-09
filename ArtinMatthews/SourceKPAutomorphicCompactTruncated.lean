module

public import ArtinMatthews.SourceKPAutomorphicCompactCutoff
public import ArtinMatthews.SourceKPAutomorphicCompactEisenstein


set_option backward.privateInPublic true
@[expose] public section

/-! The literal difference E_s-P_s on the actual compact quotient. -/
namespace ArtinMatthews
open NumberField
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAutomorphicCompactTruncatedEisenstein (T : ℝ) (s : ℂ)
    (x : SourceKPAutomorphicCompactLevel K hζ) : ℂ :=
  sourceKPAutomorphicCompactEisenstein K hζ s x-
    sourceKPAutomorphicCompactCutoffEisenstein K hζ T s x

theorem sourceKPAutomorphicCompactTruncatedEisenstein_mk (T : ℝ) (s : ℂ)
    (x : SourceKPAutomorphicLevel K hζ) :
    sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s (sourceKPAutomorphicCompactMk K hζ x) =
      sourceKPAutomorphicEisenstein K hζ s x-sourceKPAutomorphicCutoffEisenstein K hζ T s x := rfl

theorem sourceKPAutomorphicCompactTruncatedEisenstein_adelic (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s
      (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q)) =
        sourceKPAdelicCompactEisenstein K hζ s q-sourceKPAdelicCutoffEisenstein K hζ T s q := rfl

theorem sourceKPAutomorphicCompactTruncatedEisenstein_center (T : ℝ) (s : ℂ)
    (z : rootsOfUnity 3 K) (x : SourceKPAutomorphicCompactLevel K hζ) :
    sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s (z • x) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ)*
        sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s x := by
  unfold sourceKPAutomorphicCompactTruncatedEisenstein
  rw [sourceKPAutomorphicCompactEisenstein_center,sourceKPAutomorphicCompactCutoffEisenstein_center,
    mul_sub]

theorem sourceKPAutomorphicCompactTruncatedEisenstein_holomorphic {T : ℝ} (hT : 0 < T)
    (x : SourceKPAutomorphicCompactLevel K hζ) :
    DifferentiableOn ℂ (fun s => sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s x)
      {s : ℂ | ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) < 2*s.re+1} :=
  (sourceKPAutomorphicCompactEisenstein_holomorphic K hζ x).sub
    (sourceKPAutomorphicCompactCutoffEisenstein_entire K hζ hT x).differentiableOn

end
end ArtinMatthews
