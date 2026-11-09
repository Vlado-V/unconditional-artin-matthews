module

public import ArtinMatthews.SourceKPAdelicProductSection
public import ArtinMatthews.SourceKPAdelicEisensteinHolomorphic


set_option backward.privateInPublic true
@[expose] public section

/-! Actual rational summands and the Eisenstein series in the full
product of upper-half-space coordinates. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix OAI.CubicEisenstein SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing ContDiff BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicRationalProductChart (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (c : SourceKPRationalBorelCoset K) (p : InfinitePlace K → EuclideanSpatial) : ℂ :=
  if hp : ∀ v, 0 < p v 2 then
    sourceKPAdelicRationalSummand K hζ
      (sourceKPAdelicPrincipalSeriesScalar K hζ s (sourceKPAdelicCompactSection K hζ s))
      (q*(ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),1)) c else 0

theorem sourceKPAdelicRationalProductChart_mk (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (γ : PGL(2,K)) :
    sourceKPAdelicRationalProductChart K hζ s q (sourceKPRationalBorelCosetMk K γ) =
      sourceKPAdelicProductSection K hζ s (sourceKPAdelicProjectiveRationalLift K hζ γ*q) := by
  funext p
  unfold sourceKPAdelicRationalProductChart sourceKPAdelicProductSection
  split_ifs with hp
  · change sourceKPAdelicCompactScalar K hζ s
      (sourceKPAdelicProjectiveRationalLift K hζ γ*(q*(ProjGenLinGroup.mk _,1))) =
        sourceKPAdelicCompactScalar K hζ s
          ((sourceKPAdelicProjectiveRationalLift K hζ γ*q)*(ProjGenLinGroup.mk _,1))
    rw [mul_assoc]
  · rfl

theorem sourceKPAdelicRationalProductChart_contDiffAt (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (c : SourceKPRationalBorelCoset K)
    (p : InfinitePlace K → EuclideanSpatial) (hp : ∀ v, 0 < p v 2) :
    ContDiffAt ℝ (∞ : ℕ∞ω) (sourceKPAdelicRationalProductChart K hζ s q c) p := by
  induction c using Quotient.inductionOn with
  | _ γ =>
    have h := sourceKPAdelicProductSection_contDiffAt K hζ s
      (sourceKPAdelicProjectiveRationalLift K hζ γ*q) p hp
    rw [← sourceKPAdelicRationalProductChart_mk] at h
    exact h

theorem sourceKPAdelicRationalProductChart_laplacian (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (c : SourceKPRationalBorelCoset K)
    (p : InfinitePlace K → EuclideanSpatial) (hp : ∀ v, 0 < p v 2) :
    sourceArchProductCoordinateLaplacian (sourceKPAdelicRationalProductChart K hζ s q c) p =
      (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2)*
        sourceKPAdelicRationalProductChart K hζ s q c p := by
  induction c using Quotient.inductionOn with
  | _ γ =>
    have h := sourceKPAdelicProductSection_laplacian K hζ s
      (sourceKPAdelicProjectiveRationalLift K hζ γ*q) p hp
    rw [← sourceKPAdelicRationalProductChart_mk] at h
    exact h

def sourceKPAdelicEisensteinProductChart (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (p : InfinitePlace K → EuclideanSpatial) : ℂ :=
  if hp : ∀ v, 0 < p v 2 then sourceKPAdelicCompactEisenstein K hζ s
    (q*(ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),1)) else 0

theorem sourceKPAdelicEisensteinProductChart_tsum (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (p : InfinitePlace K → EuclideanSpatial) :
    sourceKPAdelicEisensteinProductChart K hζ s q p =
      ∑' c : SourceKPRationalBorelCoset K, sourceKPAdelicRationalProductChart K hζ s q c p := by
  by_cases hp : ∀ v, 0 < p v 2
  · simp only [sourceKPAdelicEisensteinProductChart, sourceKPAdelicRationalProductChart,
      dite_eq_left hp]
    rfl
  · simp only [sourceKPAdelicEisensteinProductChart, sourceKPAdelicRationalProductChart,
      dite_eq_right hp,tsum_zero]

end
end ArtinMatthews
