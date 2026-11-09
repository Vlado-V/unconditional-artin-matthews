module

public import ArtinMatthews.SourceArchProductCasimir
public import ArtinMatthews.SourceArchSectionFactorization


set_option backward.privateInPublic true
@[expose] public section

/-! The actual all-place spherical section in independent upper-halfspace coordinates. -/
namespace ArtinMatthews
open NumberField Matrix OAI.CubicEisenstein SourceArchJacquet
open scoped NumberField MatrixGroups BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceArchUpperHalfspaceMatrix (p : InfinitePlace K → EuclideanSpatial)
    (hp : ∀ v, 0 < p v 2) : GL (Fin 2) (InfiniteAdeleRing K) :=
  (sourceArchGLPiEquiv K).symm (fun v => (sourceKPArchMatrixComplexEquiv K hζ v).symm
    (upperSection ((p v 0 : ℂ) + (p v 1 : ℂ) * Complex.I) (p v 2) (hp v) : GL (Fin 2) ℂ))

theorem sourceArchSphericalProduct_upperHalfspace (s : ℂ)
    (p : InfinitePlace K → EuclideanSpatial) (hp : ∀ v, 0 < p v 2) :
    sourceArchSphericalProduct K hζ s (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp)) =
      sourceArchCoordinateProduct s p := by
  rw [sourceArchSphericalProduct_mk]
  unfold sourceArchUpperHalfspaceMatrix sourceArchCoordinateProduct
  simp only [MulEquiv.apply_symm_apply]
  apply Finset.prod_congr rfl
  intro v _
  rw [sourceArchSphericalGL_upperSection, sourceArchCoordinateProfile,
    positiveHeightPower_eq_cpow _ _ (hp v)]

theorem sourceArchSphericalProduct_coordinate_eigen (s c : ℂ)
    (p : InfinitePlace K → EuclideanSpatial) (hp : ∀ v, 0 < p v 2) :
    sourceArchProductCoordinateLaplacian (fun q => c * sourceArchCoordinateProduct s q) p =
      (InfinitePlace.nrComplexPlaces K : ℂ) * (1 - 4 * s ^ 2) *
        (c * sourceArchSphericalProduct K hζ s
          (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp))) := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  have hcard : Fintype.card (InfinitePlace K) = InfinitePlace.nrComplexPlaces K := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  rw [sourceArchSphericalProduct_upperHalfspace]
  simpa only [hcard] using sourceArchCoordinateProduct_laplacian s c p hp

theorem sourceArchCompactScalar_coordinate_eigen (s : ℂ)
    (qf : SourceKPFiniteAdeleProjective K hζ)
    (p : InfinitePlace K → EuclideanSpatial) (hp : ∀ v, 0 < p v 2) :
    sourceArchProductCoordinateLaplacian
        (fun q => sourceArchCoordinateProduct s q * sourceKPAdelicCompactScalar K hζ s (1, qf)) p =
      (InfinitePlace.nrComplexPlaces K : ℂ) * (1 - 4 * s ^ 2) *
        sourceKPAdelicCompactScalar K hζ s
          (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp), qf) := by
  rw [sourceArchCompactScalar_factor K hζ s
    (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp)) qf,
    sourceArchSphericalProduct_upperHalfspace]
  have h := sourceArchSphericalProduct_coordinate_eigen K hζ s
    (sourceKPAdelicCompactScalar K hζ s (1, qf)) p hp
  rw [sourceArchSphericalProduct_upperHalfspace] at h
  simpa only [mul_comm] using h

end
end ArtinMatthews
