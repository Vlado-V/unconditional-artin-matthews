module

public import ArtinMatthews.SourceKPFiniteLevelDescent
public import ArtinMatthews.SourceKPAdelicEisensteinHolomorphic


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact-section Eisenstein series descends to the actual
rational quotient at its finite level. Analytic statements below retain the
proved initial half-plane. -/

namespace ArtinMatthews
open NumberField Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCompactScalar_finite_right (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (k : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPAdelicCompactScalar K hζ s (g * sourceKPFiniteDeepCoverLift K hζ k) =
      sourceKPAdelicCompactScalar K hζ s g := by
  have he := sourceKPAdelicCompactSection_finite_fixed K hζ s k
  rw [← sourceKPFiniteDeepCoverLift_eq] at he
  exact congrArg (fun f : SourceKPAdelicPrincipalSeries K hζ s => (f.val g).val 1) he

theorem sourceKPAdelicCompactEisenstein_finite_right (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (k : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPAdelicCompactEisenstein K hζ s (g * sourceKPFiniteDeepCoverLift K hζ k) =
      sourceKPAdelicCompactEisenstein K hζ s g := by
  unfold sourceKPAdelicCompactEisenstein sourceKPAdelicEisensteinSum sourceKPAdelicRationalSum
  apply tsum_congr
  intro q
  induction q using Quotient.inductionOn with
  | _ a =>
    change sourceKPAdelicCompactScalar K hζ s
      (sourceKPAdelicProjectiveRationalLift K hζ a * (g * sourceKPFiniteDeepCoverLift K hζ k)) = _
    rw [← mul_assoc]
    exact sourceKPAdelicCompactScalar_finite_right K hζ s _ k

theorem sourceKPAdelicCompactEisenstein_rational_invariant (s : ℂ)
    (γ : PGL(2, K)) (g : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicProjectiveRationalLift K hζ γ * g) =
      sourceKPAdelicCompactEisenstein K hζ s g :=
  sourceKPAdelicRationalSum_automorphy K hζ
    (sourceKPAdelicPrincipalSeriesScalar K hζ s (sourceKPAdelicCompactSection K hζ s)) γ g

def sourceKPAutomorphicEisenstein (s : ℂ) : SourceKPAutomorphicLevel K hζ → ℂ :=
  sourceKPAutomorphicLevelDescend K hζ (sourceKPAdelicCompactEisenstein K hζ s)
    (sourceKPAdelicCompactEisenstein_finite_right K hζ s)
    (sourceKPAdelicCompactEisenstein_rational_invariant K hζ s)

theorem sourceKPAutomorphicEisenstein_mk (s : ℂ) (g : SourceKPAdelicProjective K hζ) :
    sourceKPAutomorphicEisenstein K hζ s (sourceKPAutomorphicLevelMk K hζ g) =
      sourceKPAdelicCompactEisenstein K hζ s g := rfl

theorem sourceKPAutomorphicEisenstein_holomorphic (x : SourceKPAutomorphicLevel K hζ) :
    DifferentiableOn ℂ (fun s => sourceKPAutomorphicEisenstein K hζ s x)
      {s : ℂ | ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) < 2*s.re+1} := by
  obtain ⟨g,rfl⟩ := sourceKPAutomorphicLevelMk_surjective K hζ x
  exact sourceKPAdelicCompactEisenstein_holomorphic K hζ g

end
end ArtinMatthews
