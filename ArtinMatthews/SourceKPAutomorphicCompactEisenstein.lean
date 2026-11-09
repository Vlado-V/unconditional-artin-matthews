module

public import ArtinMatthews.SourceKPAutomorphicEisenstein
public import ArtinMatthews.SourceKPCompactHeight
public import ArtinMatthews.SourceKPCubicCompactAction


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact-section Eisenstein sum descends to the compact
quotient, retaining its literal adelic value and forward cubic character. -/
namespace ArtinMatthews
open NumberField Matrix Topology MulOpposite
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCompactScalar_right_deep (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (k : sourceKPAdelicDeepCompact K hζ) :
    sourceKPAdelicCompactScalar K hζ s (q*k.val) = sourceKPAdelicCompactScalar K hζ s q :=
  congrArg (fun f : SourceKPAdelicPrincipalSeries K hζ s => (f.val q).val 1)
    (sourceKPAdelicCompactSection_right K hζ s k)

theorem sourceKPAdelicCompactEisenstein_right_deep (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (k : sourceKPAdelicDeepCompact K hζ) :
    sourceKPAdelicCompactEisenstein K hζ s (q*k.val) =
      sourceKPAdelicCompactEisenstein K hζ s q := by
  unfold sourceKPAdelicCompactEisenstein sourceKPAdelicEisensteinSum sourceKPAdelicRationalSum
  apply tsum_congr
  intro c
  induction c using Quotient.inductionOn with
  | _ γ =>
    change sourceKPAdelicCompactScalar K hζ s
      (sourceKPAdelicProjectiveRationalLift K hζ γ*(q*k.val)) = _
    rw [← mul_assoc,sourceKPAdelicCompactScalar_right_deep]
    rfl

theorem sourceKPAdelicCompactEisenstein_center (s : ℂ) (z : rootsOfUnity 3 K)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicProjectiveCenter K hζ z*q) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ)*sourceKPAdelicCompactEisenstein K hζ s q :=
  sourceKPAdelicEisensteinSum_center K hζ s (sourceKPAdelicCompactSection K hζ s) z q

theorem sourceKPAutomorphicEisenstein_rightCompact (s : ℂ)
    (k : SourceKPArchCompactRightGroup K hζ) (x : SourceKPAutomorphicLevel K hζ) :
    sourceKPAutomorphicEisenstein K hζ s (k • x) = sourceKPAutomorphicEisenstein K hζ s x := by
  obtain ⟨q,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
  calc
    _ = sourceKPAutomorphicEisenstein K hζ s
        (sourceKPAutomorphicLevelMk K hζ (q.1*unop k.val,q.2)) :=
      congrArg (sourceKPAutomorphicEisenstein K hζ s)
        (sourceKPAutomorphicLevelMk_archRight K hζ k.val q)
    _ = _ := by
      rw [sourceKPAutomorphicEisenstein_mk,sourceKPAutomorphicEisenstein_mk]
      have hp : (q.1*unop k.val,q.2) = q*((unop k.val,1) : SourceKPAdelicProjective K hζ) :=
        Prod.ext rfl (mul_one q.2).symm
      rw [hp]
      exact sourceKPAdelicCompactEisenstein_right_deep K hζ s q
        ⟨(unop k.val,1),sourceKPArchCompactRight_deep K hζ k⟩

def sourceKPAutomorphicCompactEisenstein (s : ℂ) :
    SourceKPAutomorphicCompactLevel K hζ → ℂ :=
  Quotient.lift (sourceKPAutomorphicEisenstein K hζ s) (by
    intro x y hxy
    obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp hxy
    rw [← hk]
    exact sourceKPAutomorphicEisenstein_rightCompact K hζ s k y)

theorem sourceKPAutomorphicCompactEisenstein_mk (s : ℂ) (x : SourceKPAutomorphicLevel K hζ) :
    sourceKPAutomorphicCompactEisenstein K hζ s (sourceKPAutomorphicCompactMk K hζ x) =
      sourceKPAutomorphicEisenstein K hζ s x := rfl

theorem sourceKPAutomorphicCompactEisenstein_adelic (s : ℂ) (q : SourceKPAdelicProjective K hζ) :
    sourceKPAutomorphicCompactEisenstein K hζ s
      (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q)) =
        sourceKPAdelicCompactEisenstein K hζ s q := rfl

theorem sourceKPAutomorphicCompactEisenstein_holomorphic (x : SourceKPAutomorphicCompactLevel K hζ) :
    DifferentiableOn ℂ (fun s => sourceKPAutomorphicCompactEisenstein K hζ s x)
      {s : ℂ | ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) < 2*s.re+1} := by
  induction x using Quotient.inductionOn with
  | _ x => exact sourceKPAutomorphicEisenstein_holomorphic K hζ x

theorem sourceKPAutomorphicCompactEisenstein_center (s : ℂ) (z : rootsOfUnity 3 K)
    (x : SourceKPAutomorphicCompactLevel K hζ) :
    sourceKPAutomorphicCompactEisenstein K hζ s (z • x) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ)*sourceKPAutomorphicCompactEisenstein K hζ s x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    obtain ⟨q,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
    change sourceKPAutomorphicCompactEisenstein K hζ s
      (z • sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q)) = _
    rw [sourceKPCubicCenter_compact_mk,sourceKPCubicCenter_automorphic_mk]
    change sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicProjectiveCenter K hζ z*q) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ)*sourceKPAdelicCompactEisenstein K hζ s q
    exact sourceKPAdelicCompactEisenstein_center K hζ s z q

end
end ArtinMatthews
