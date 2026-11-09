module

public import ArtinMatthews.SourceKPAdelicCutoffDefect
public import ArtinMatthews.SourceAdelicOrbitHeightTopology


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite-level automorphic cusp cutoff and its Casimir
defect. The defect's topological support lies in a closed orbit-height sublevel. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCutoffEisenstein_finite_right (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (k : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPAdelicCutoffEisenstein K hζ T s (q*sourceKPFiniteDeepCoverLift K hζ k) =
      sourceKPAdelicCutoffEisenstein K hζ T s q :=
  sourceKPAdelicCutoffEisenstein_right K hζ T s q
    ⟨sourceKPFiniteDeepCoverLift K hζ k, ⟨sourceKPFiniteDeepIntoAdelic K hζ k,rfl⟩⟩

theorem sourceArchGlobalCasimir_finite_right
    (f : SourceKPAdelicProjective K hζ → ℂ)
    (hf : ∀ q k, f (q*sourceKPFiniteDeepCoverLift K hζ k) = f q)
    (q : SourceKPAdelicProjective K hζ) (k : sourceKPFiniteDeepMatrixGroup K)
    (v : InfinitePlace K) :
    sourceArchGlobalCasimir K hζ f (q*sourceKPFiniteDeepCoverLift K hζ k) v =
      sourceArchGlobalCasimir K hζ f q v := by
  have hc (a : GL (Fin 2) ℂ) :
      sourceKPFiniteDeepCoverLift K hζ k*sourceArchGroupSingle K hζ v a =
        sourceArchGroupSingle K hζ v a*sourceKPFiniteDeepCoverLift K hζ k := by
    apply Prod.ext
    · change (sourceKPFiniteDeepCoverLift K hζ k).1 * _ = _ * (sourceKPFiniteDeepCoverLift K hζ k).1
      rw [sourceKPFiniteDeepCoverLift_fst, one_mul, mul_one]
    · change (sourceKPFiniteDeepCoverLift K hζ k).2 * 1 = 1 * (sourceKPFiniteDeepCoverLift K hζ k).2
      rw [mul_one,one_mul]
  have hU (z : ℂ) : sourceArchGlobalUpperTranslate K hζ f
      (q*sourceKPFiniteDeepCoverLift K hζ k) v z = sourceArchGlobalUpperTranslate K hζ f q v z := by
    funext t
    unfold sourceArchGlobalUpperTranslate
    rw [mul_assoc, hc, ← mul_assoc, hf]
  have hA : sourceArchGlobalDiagonalTranslate K hζ f
      (q*sourceKPFiniteDeepCoverLift K hζ k) v = sourceArchGlobalDiagonalTranslate K hζ f q v := by
    funext t
    unfold sourceArchGlobalDiagonalTranslate
    rw [mul_assoc, hc, ← mul_assoc, hf]
  unfold sourceArchGlobalCasimir
  rw [hU 1,hU Complex.I,hA]

theorem sourceKPAdelicCutoffCasimirDefect_finite_right (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (k : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPAdelicCutoffCasimirDefect K hζ T s (q*sourceKPFiniteDeepCoverLift K hζ k) =
      sourceKPAdelicCutoffCasimirDefect K hζ T s q := by
  unfold sourceKPAdelicCutoffCasimirDefect
  simp_rw [sourceArchGlobalCasimir_finite_right K hζ _
    (sourceKPAdelicCutoffEisenstein_finite_right K hζ T s),
    sourceKPAdelicCutoffEisenstein_finite_right]

def sourceKPAutomorphicCutoffEisenstein (T : ℝ) (s : ℂ) : SourceKPAutomorphicLevel K hζ → ℂ :=
  sourceKPAutomorphicLevelDescend K hζ (sourceKPAdelicCutoffEisenstein K hζ T s)
    (sourceKPAdelicCutoffEisenstein_finite_right K hζ T s)
    (sourceKPAdelicCutoffEisenstein_rational K hζ T s)

def sourceKPAutomorphicCutoffDefect (T : ℝ) (s : ℂ) : SourceKPAutomorphicLevel K hζ → ℂ :=
  sourceKPAutomorphicLevelDescend K hζ (sourceKPAdelicCutoffCasimirDefect K hζ T s)
    (sourceKPAdelicCutoffCasimirDefect_finite_right K hζ T s)
    (sourceKPAdelicCutoffCasimirDefect_rational K hζ T s)

theorem sourceKPAutomorphicCutoffEisenstein_mk (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAutomorphicCutoffEisenstein K hζ T s (sourceKPAutomorphicLevelMk K hζ q) =
      sourceKPAdelicCutoffEisenstein K hζ T s q := rfl

theorem sourceKPAutomorphicCutoffDefect_mk (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAutomorphicCutoffDefect K hζ T s (sourceKPAutomorphicLevelMk K hζ q) =
      sourceKPAdelicCutoffCasimirDefect K hζ T s q := rfl

theorem sourceKPAutomorphicCutoffEisenstein_entire {T : ℝ} (hT : 0 < T)
    (x : SourceKPAutomorphicLevel K hζ) :
    Differentiable ℂ (fun s => sourceKPAutomorphicCutoffEisenstein K hζ T s x) := by
  obtain ⟨q,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
  exact sourceKPAdelicCutoffEisenstein_entire K hζ hT q

theorem sourceKPAutomorphicCutoffDefect_support {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    Function.support (sourceKPAutomorphicCutoffDefect K hζ T s) ⊆
      {x : SourceKPAutomorphicLevel K hζ | sourceKPAutomorphicOrbitHeight K hζ x ≤ 2*T} := by
  intro x hx
  obtain ⟨q,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
  exact sourceKPAdelicCutoffCasimirDefect_support K hζ hT s hx

theorem sourceKPAutomorphicCutoffDefect_tsupport {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    tsupport (sourceKPAutomorphicCutoffDefect K hζ T s) ⊆
      {x : SourceKPAutomorphicLevel K hζ | sourceKPAutomorphicOrbitHeight K hζ x ≤ 2*T} :=
  closure_minimal (sourceKPAutomorphicCutoffDefect_support K hζ hT s)
    (sourceKPAutomorphicOrbitHeight_sublevel_closed K hζ (2*T))

end
end ArtinMatthews
