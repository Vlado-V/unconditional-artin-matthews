module

public import ArtinMatthews.SourceKPAutomorphicCutoff
public import ArtinMatthews.SourceKPCompactHeight
public import ArtinMatthews.SourceKPAdelicCutoffGenuine
public import ArtinMatthews.SourceKPCubicCompactAction


set_option backward.privateInPublic true
@[expose] public section

/-! The literal cusp cutoff descends through the actual right compact
quotient and retains its forward cubic central character. -/
namespace ArtinMatthews
open NumberField Matrix Topology MulOpposite
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAutomorphicCutoffEisenstein_rightCompact (T : ℝ) (s : ℂ)
    (k : SourceKPArchCompactRightGroup K hζ) (x : SourceKPAutomorphicLevel K hζ) :
    sourceKPAutomorphicCutoffEisenstein K hζ T s (k • x) =
      sourceKPAutomorphicCutoffEisenstein K hζ T s x := by
  obtain ⟨q,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
  calc
    _ = sourceKPAutomorphicCutoffEisenstein K hζ T s
        (sourceKPAutomorphicLevelMk K hζ (q.1*unop k.val,q.2)) :=
      congrArg (sourceKPAutomorphicCutoffEisenstein K hζ T s)
        (sourceKPAutomorphicLevelMk_archRight K hζ k.val q)
    _ = _ := by
      rw [sourceKPAutomorphicCutoffEisenstein_mk,sourceKPAutomorphicCutoffEisenstein_mk]
      have hp : (q.1*unop k.val,q.2) = q*((unop k.val,1) : SourceKPAdelicProjective K hζ) :=
        Prod.ext rfl (mul_one q.2).symm
      rw [hp]
      exact sourceKPAdelicCutoffEisenstein_right K hζ T s q
        ⟨(unop k.val,1),sourceKPArchCompactRight_deep K hζ k⟩

def sourceKPAutomorphicCompactCutoffEisenstein (T : ℝ) (s : ℂ) :
    SourceKPAutomorphicCompactLevel K hζ → ℂ :=
  Quotient.lift (sourceKPAutomorphicCutoffEisenstein K hζ T s) (by
    intro x y hxy
    obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp hxy
    rw [← hk]
    exact sourceKPAutomorphicCutoffEisenstein_rightCompact K hζ T s k y)

theorem sourceKPAutomorphicCompactCutoffEisenstein_mk (T : ℝ) (s : ℂ)
    (x : SourceKPAutomorphicLevel K hζ) :
    sourceKPAutomorphicCompactCutoffEisenstein K hζ T s (sourceKPAutomorphicCompactMk K hζ x) =
      sourceKPAutomorphicCutoffEisenstein K hζ T s x := rfl

theorem sourceKPAutomorphicCompactCutoffEisenstein_adelic (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAutomorphicCompactCutoffEisenstein K hζ T s
      (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q)) =
        sourceKPAdelicCutoffEisenstein K hζ T s q := rfl

theorem sourceKPAutomorphicCompactCutoffEisenstein_entire {T : ℝ} (hT : 0 < T)
    (x : SourceKPAutomorphicCompactLevel K hζ) :
    Differentiable ℂ (fun s => sourceKPAutomorphicCompactCutoffEisenstein K hζ T s x) := by
  induction x using Quotient.inductionOn with
  | _ x => exact sourceKPAutomorphicCutoffEisenstein_entire K hζ hT x

theorem sourceKPAutomorphicCompactCutoffEisenstein_center (T : ℝ) (s : ℂ)
    (z : rootsOfUnity 3 K) (x : SourceKPAutomorphicCompactLevel K hζ) :
    sourceKPAutomorphicCompactCutoffEisenstein K hζ T s (z • x) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ)*
        sourceKPAutomorphicCompactCutoffEisenstein K hζ T s x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    obtain ⟨q,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
    change sourceKPAutomorphicCompactCutoffEisenstein K hζ T s
      (z • sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q)) = _
    rw [sourceKPCubicCenter_compact_mk,sourceKPCubicCenter_automorphic_mk]
    change sourceKPAdelicCutoffEisenstein K hζ T s (sourceKPAdelicProjectiveCenter K hζ z*q) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ)*sourceKPAdelicCutoffEisenstein K hζ T s q
    exact sourceKPAdelicCutoffEisenstein_center K hζ T s z q

end
end ArtinMatthews
