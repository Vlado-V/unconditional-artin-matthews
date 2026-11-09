module

public import ArtinMatthews.SourceKPAdelicCompactIntersection
public import ArtinMatthews.SourceKPAdelicUnitAnalytic
public import ArtinMatthews.SourceCompactInduction


set_option backward.privateInPublic true
@[expose] public section

/-! The actual full adelic induced section supported on B K, where K
has the checked tame integral and wild deep-congruence splitting. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCompactBorel_torus
    (b : sourceKPAdelicCoveringBorel K hζ) (k : sourceKPAdelicDeepCompact K hζ)
    (he : b.val = k.val) :
    ∃ u : sourceKPAdelicUnitTorus K hζ, sourceKPAdelicBorelTorusProjection K hζ b = u.val := by
  obtain ⟨g,hg⟩ := k.property
  have hb : ProjGenLinGroup.mk g.val ∈ sourceKPRingBorel 𝔸[K] := by
    rw [← sourceKPAdelicDeepCompactLift_projection, hg, ← he]
    exact b.property
  obtain ⟨x,a,ha⟩ := sourceKPAdelicDeepCompact_triangular K hζ g hb
  let t : sourceKPAdelicCoveringTorus K hζ :=
    ⟨sourceKPAdelicProjectiveDiagonalLift K hζ a.val,
      sourceKPAdelicCoveringTorus_diagonal_mem K hζ a.val⟩
  let u : sourceKPAdelicUnitTorus K hζ := ⟨t, ⟨a,rfl⟩⟩
  have hcoord : b = sourceKPAdelicBorelCoordinatesEquiv K hζ (x,u.val) := by
    apply Subtype.ext
    change b.val = sourceKPAdelicUpperLift K hζ x * sourceKPAdelicProjectiveDiagonalLift K hζ a.val
    rw [he, ← hg]
    exact ha
  refine ⟨u, ?_⟩
  rw [hcoord, sourceKPAdelicBorelTorusProjection_coordinates]

theorem sourceKPAdelicCompactBorel_modularHalf
    (b : sourceKPAdelicCoveringBorel K hζ) (u : sourceKPAdelicUnitTorus K hζ)
    (he : sourceKPAdelicBorelTorusProjection K hζ b = u.val) :
    sourceKPAdelicBorelModularHalf K hζ b = 1 := by
  change (sourceKPIdeleComplexNorm K (1/2 : ℂ)
    (sourceKPAdelicTorusIdele K hζ (sourceKPAdelicBorelTorusProjection K hζ b)) : ℂ) = 1
  rw [he, sourceKPIdeleComplexNorm_coe, sourceKPAdelicUnitTorus_ideleNorm,
    Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

theorem sourceKPAdelicCompactBorel_fixed (s : ℂ)
    (b : sourceKPAdelicCoveringBorel K hζ) (k : sourceKPAdelicDeepCompact K hζ)
    (he : b.val = k.val) :
    sourceKPAdelicNormalizedBorelRepresentation K hζ s b
      (sourceKPAdelicUnitSphericalVector K hζ s) = sourceKPAdelicUnitSphericalVector K hζ s := by
  obtain ⟨u,hu⟩ := sourceKPAdelicCompactBorel_torus K hζ b k he
  change sourceKPAdelicBorelModularHalf K hζ b •
    sourceKPAdelicTorusInducedRepresentation K hζ s (sourceKPAdelicBorelTorusProjection K hζ b)
      (sourceKPAdelicUnitSphericalVector K hζ s) = _
  rw [sourceKPAdelicCompactBorel_modularHalf K hζ b u hu, one_smul, hu,
    sourceKPAdelicUnitSphericalVector_right]

def sourceKPAdelicCompactSection (s : ℂ) : SourceKPAdelicPrincipalSeries K hζ s :=
  sourceCompactInducedSection (sourceKPAdelicCoveringBorel K hζ)
    (sourceKPAdelicNormalizedBorelRepresentation K hζ s) (sourceKPAdelicDeepCompact K hζ)
    (sourceKPAdelicUnitSphericalVector K hζ s) (sourceKPAdelicCompactBorel_fixed K hζ s)

theorem sourceKPAdelicCompactSection_factor (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (b : sourceKPAdelicCoveringBorel K hζ)
    (k : sourceKPAdelicDeepCompact K hζ) (he : g = b.val*k.val) :
    (sourceKPAdelicCompactSection K hζ s).val g =
      sourceKPAdelicNormalizedBorelRepresentation K hζ s b (sourceKPAdelicUnitSphericalVector K hζ s) :=
  sourceCompactInducedSection_factor _ _ _ _ _ he

theorem sourceKPAdelicCompactSection_one (s : ℂ) :
    (sourceKPAdelicCompactSection K hζ s).val 1 = sourceKPAdelicUnitSphericalVector K hζ s :=
  sourceCompactInducedSection_one _ _ _ _ _

theorem sourceKPAdelicCompactSection_ne_zero (s : ℂ) : sourceKPAdelicCompactSection K hζ s ≠ 0 := by
  intro he
  have h := congrArg (fun f : SourceKPAdelicPrincipalSeries K hζ s => f.val 1) he
  rw [sourceKPAdelicCompactSection_one] at h
  exact sourceKPAdelicUnitSphericalVector_ne_zero K hζ s h

theorem sourceKPAdelicCompactSection_right (s : ℂ) (k : sourceKPAdelicDeepCompact K hζ) :
    sourceKPAdelicPrincipalSeriesRepresentation K hζ s k.val (sourceKPAdelicCompactSection K hζ s) =
      sourceKPAdelicCompactSection K hζ s :=
  sourceCompactInducedSection_right _ _ _ _ _ k

def sourceKPAdelicCompactScalar (s : ℂ) (g : SourceKPAdelicProjective K hζ) : ℂ :=
  ((sourceKPAdelicCompactSection K hζ s).val g).val 1

theorem sourceKPAdelicCompactScalar_one (s : ℂ) : sourceKPAdelicCompactScalar K hζ s 1 = 1 := by
  unfold sourceKPAdelicCompactScalar
  rw [sourceKPAdelicCompactSection_one, sourceKPAdelicUnitSphericalVector_one]

theorem sourceKPAdelicCompactScalar_zero (s : ℂ) (g : SourceKPAdelicProjective K hζ)
    (hg : ¬sourceCompactInducedFactorable (sourceKPAdelicCoveringBorel K hζ)
      (sourceKPAdelicDeepCompact K hζ) g) : sourceKPAdelicCompactScalar K hζ s g = 0 := by
  change (sourceCompactInducedValue (sourceKPAdelicCoveringBorel K hζ)
    (sourceKPAdelicNormalizedBorelRepresentation K hζ s) (sourceKPAdelicDeepCompact K hζ)
    (sourceKPAdelicUnitSphericalVector K hζ s) g).val 1 = 0
  rw [sourceCompactInducedValue_zero _ _ _ _ hg]
  rfl

theorem sourceKPAdelicCompactScalar_entire (g : SourceKPAdelicProjective K hζ) :
    Differentiable ℂ (fun s : ℂ => sourceKPAdelicCompactScalar K hζ s g) := by
  by_cases hg : sourceCompactInducedFactorable (sourceKPAdelicCoveringBorel K hζ)
      (sourceKPAdelicDeepCompact K hζ) g
  · obtain ⟨b,k,he⟩ := hg
    have hval (s : ℂ) : sourceKPAdelicCompactScalar K hζ s g =
        (sourceKPAdelicNormalizedBorelRepresentation K hζ s b
          (sourceKPAdelicUnitSphericalVector K hζ s)).val 1 := by
      unfold sourceKPAdelicCompactScalar
      rw [sourceKPAdelicCompactSection_factor K hζ s g b k he]
    simp_rw [hval]
    exact sourceKPAdelicUnitSphericalVector_normalizedBorel_entire K hζ b
  · have hval (s : ℂ) := sourceKPAdelicCompactScalar_zero K hζ s g hg
    simp_rw [hval]
    exact differentiable_const (0 : ℂ)

theorem sourceKPAdelicCompactScalar_factor_bound (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (b : sourceKPAdelicCoveringBorel K hζ)
    (k : sourceKPAdelicDeepCompact K hζ) (he : g = b.val*k.val) :
    ‖sourceKPAdelicCompactScalar K hζ s g‖ ≤
      (sourceKPIdeleAbsoluteNorm K (sourceKPAdelicTorusIdele K hζ
        (sourceKPAdelicBorelTorusProjection K hζ b))) ^ (s.re+1/2) := by
  unfold sourceKPAdelicCompactScalar
  rw [sourceKPAdelicCompactSection_factor K hζ s g b k he]
  exact sourceKPAdelicUnitSphericalVector_normalizedBorel_bound K hζ s b

end
end ArtinMatthews
