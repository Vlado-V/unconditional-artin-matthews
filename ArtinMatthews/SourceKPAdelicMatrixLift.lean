module

public import ArtinMatthews.SourceKPCompactBorelPhase
public import ArtinMatthews.SourceKPAdelicBorel
public import ArtinMatthews.SourceKPAdelicCompactSplit
public import ArtinMatthews.SourceKPAdelicUnitTorus


set_option backward.privateInPublic true
@[expose] public section

/-! The phase-one matrix section and the exact normalization of its
compact triangular representatives. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicMatrixLift (g : GL (Fin 2) 𝔸[K]) : SourceKPAdelicProjective K hζ :=
  (ProjGenLinGroup.mk ((sourceKPGL2ProductEquiv K g).1),
    sourceKPFiniteAdeleProjectiveLift K hζ ((sourceKPGL2ProductEquiv K g).2))

theorem sourceKPAdelicMatrixLift_projection (g : GL (Fin 2) 𝔸[K]) :
    sourceKPAdelicProjectiveProjection K hζ (sourceKPAdelicMatrixLift K hζ g) =
      ProjGenLinGroup.mk g := by
  apply (sourceKPAdelicProjectiveProductEquiv K).injective
  rw [sourceKPAdelicProjectiveProjection_product]
  rfl

theorem sourceKPAdelicMatrixLift_deepCompact (g : sourceKPAdelicDeepCompactMatrix K hζ) :
    sourceKPAdelicMatrixLift K hζ g.val = sourceKPAdelicDeepCompactLift K hζ g := rfl

theorem sourceKPGL2ProductEquiv_upper (x : 𝔸[K]) :
    sourceKPGL2ProductEquiv K (sourceKPUpperMatrix 𝔸[K] x) =
      (sourceKPUpperMatrix (InfiniteAdeleRing K) x.1, sourceKPUpperMatrix 𝔸ᶠ[K] x.2) := by
  apply Prod.ext <;> apply GeneralLinearGroup.ext <;> intro i j <;>
    fin_cases i <;> fin_cases j <;> rfl

theorem sourceKPGL2ProductEquiv_diagonal (a : IdeleGroup (𝓞 K) K) :
    sourceKPGL2ProductEquiv K (sourceKPDiagonalHom 𝔸[K] a) =
      (sourceKPDiagonalHom (InfiniteAdeleRing K) (sourceKPIdeleInfiniteUnit K a),
        sourceKPDiagonalHom 𝔸ᶠ[K] (sourceKPIdeleFiniteUnit K a)) := by
  apply Prod.ext <;> apply GeneralLinearGroup.ext <;> intro i j <;>
    fin_cases i <;> fin_cases j <;> rfl

theorem sourceKPAdelicMatrixLift_upper_diagonal (x : 𝔸[K]) (a : IdeleGroup (𝓞 K) K) :
    sourceKPAdelicMatrixLift K hζ (sourceKPUpperMatrix 𝔸[K] x * sourceKPDiagonalHom 𝔸[K] a) =
      sourceKPAdelicUpperLift K hζ x * sourceKPAdelicProjectiveDiagonalLift K hζ a := by
  apply Prod.ext
  · change ProjGenLinGroup.mk ((sourceKPGL2ProductEquiv K
        (sourceKPUpperMatrix 𝔸[K] x * sourceKPDiagonalHom 𝔸[K] a)).1) = _
    rw [map_mul, sourceKPGL2ProductEquiv_upper, sourceKPGL2ProductEquiv_diagonal]
    exact map_mul ProjGenLinGroup.mk _ _
  · change sourceKPFiniteAdeleProjectiveLift K hζ ((sourceKPGL2ProductEquiv K
        (sourceKPUpperMatrix 𝔸[K] x * sourceKPDiagonalHom 𝔸[K] a)).2) = _
    rw [map_mul, sourceKPGL2ProductEquiv_upper, sourceKPGL2ProductEquiv_diagonal]
    change sourceKPFiniteAdeleProjectiveLift K hζ
      (sourceKPUpperMatrix 𝔸ᶠ[K] x.2 * sourceKPDiagonalHom 𝔸ᶠ[K] (sourceKPIdeleFiniteUnit K a)) = _
    rw [
      ← sourceKPFiniteAdeleProjectiveLift_mul_of_phase_one K hζ _ _
        (sourceKPAdeleMultiplier_upper_diagonal K hζ (sourceKPIdeleFiniteUnit K a) x.2)]
    rfl

theorem sourceKPAdelicMatrixLift_normalized_scalar
    (b : GL (Fin 2) 𝔸[K]) (hb : b ∈ sourceKPRingNormalizedBorel 𝔸[K])
    (u : IdeleGroup (𝓞 K) K)
    (hu : ∀ P, sourceKPFiniteVal K P
      (sourceKPIdeleFiniteCoordinate K P u : P.adicCompletion K) = 1)
    (hbval : ∀ P, sourceKPFiniteVal K P
      (GeneralLinearGroup.det (sourceKPAdelicBaseFiniteAt K P b) : P.adicCompletion K) = 1)
    (huc : ∀ P, (6 : 𝓞 K) ∈ P.asIdeal →
      sourceKPIdeleFiniteCoordinate K P u ∈ sourceKPUnitCubes (P.adicCompletion K)) :
    sourceKPAdelicMatrixLift K hζ (b * GeneralLinearGroup.scalar (Fin 2) u) =
      sourceKPAdelicMatrixLift K hζ b := by
  apply Prod.ext
  · change ProjGenLinGroup.mk ((sourceKPGL2ProductEquiv K
        (b * GeneralLinearGroup.scalar (Fin 2) u)).1) = _
    rw [map_mul, sourceKPGL2ProductEquiv_scalar]
    change ProjGenLinGroup.mk ((sourceKPGL2ProductEquiv K b).1 *
      GeneralLinearGroup.scalar (Fin 2) (sourceKPIdeleInfiniteUnit K u)) = _
    rw [map_mul, ProjGenLinGroup.mk_scalar, mul_one]
    rfl
  · change sourceKPFiniteAdeleProjectiveLift K hζ ((sourceKPGL2ProductEquiv K
        (b * GeneralLinearGroup.scalar (Fin 2) u)).2) = _
    rw [map_mul, sourceKPGL2ProductEquiv_scalar]
    change sourceKPFiniteAdeleProjectiveLift K hζ ((sourceKPGL2ProductEquiv K b).2 *
      GeneralLinearGroup.scalar (Fin 2) (sourceKPIdeleFiniteUnit K u)) = _
    have hbf : (sourceKPGL2ProductEquiv K b).2 ∈
        sourceKPRingNormalizedBorel 𝔸ᶠ[K] := by
      constructor
      · change (b 1 0).2 = 0
        rw [hb.1]
        rfl
      · change (b 1 1).2 = 1
        rw [hb.2]
        rfl
    exact sourceKPFiniteAdeleProjectiveLift_normalized_scalar K hζ _ hbf
      (sourceKPIdeleFiniteUnit K u) hu hbval huc

end
end ArtinMatthews
