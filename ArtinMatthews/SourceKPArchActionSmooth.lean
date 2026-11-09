module

public import ArtinMatthews.SourceArchProjectiveActionSmooth
public import ArtinMatthews.SourceKPArchH1Coordinates


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField MeasureTheory SourceArchJacquet SourceHyperbolicGreen OAI.CubicEisenstein Filter
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPArchEuclideanAction (a : PGL(2,InfiniteAdeleRing K))
    (p : ProductSpace (InfinitePlace K)) : ProductSpace (InfinitePlace K) :=
  sourceKPArchUpperEuclideanMap K
    (sourceKPArchUpperAction K hζ a (sourceKPArchEuclideanUpperMap K p))

theorem sourceKPArchEuclideanAction_apply (a : PGL(2,InfiniteAdeleRing K))
    (p : ProductSpace (InfinitePlace K)) (v : InfinitePlace K) :
    sourceKPArchEuclideanAction K hζ a p v =
      sourceArchEuclideanProjectiveAction (sourceKPArchProjectiveAt K hζ v a) (p v) := rfl

theorem sourceKPArchEuclideanAction_positive (a : PGL(2,InfiniteAdeleRing K))
    (p : ProductSpace (InfinitePlace K)) :
    sourceKPArchEuclideanAction K hζ a p ∈ productUpper (InfinitePlace K) := by
  intro v _
  exact sourceArchUpperEuclideanMap_positive _

theorem sourceKPArchEuclideanAction_preserving (a : PGL(2,InfiniteAdeleRing K)) :
    MeasurePreserving (sourceKPArchEuclideanAction K hζ a)
      (productVolume (InfinitePlace K)) (productVolume (InfinitePlace K)) :=
  (sourceKPArchUpperEuclideanMap_preserving K).comp
    ((sourceKPArchUpperAction_preserving K hζ a).comp (sourceKPArchEuclideanUpperMap_preserving K))

theorem sourceKPArchEuclideanAction_contDiffAt (a : PGL(2,InfiniteAdeleRing K))
    (p : ProductSpace (InfinitePlace K)) (hp : p ∈ productUpper (InfinitePlace K)) :
    ContDiffAt ℝ (∞ : ℕ∞ω) (sourceKPArchEuclideanAction K hζ a) p := by
  apply contDiffAt_pi.mpr
  intro v
  change ContDiffAt ℝ (∞ : ℕ∞ω)
    (fun q : ProductSpace (InfinitePlace K) =>
      sourceArchEuclideanProjectiveAction (sourceKPArchProjectiveAt K hζ v a) (q v)) p
  have ho := sourceArchEuclideanProjectiveAction_contDiffAt (sourceKPArchProjectiveAt K hζ v a)
    (p v) (hp v (Set.mem_univ v))
  have hi : ContDiffAt ℝ (∞ : ℕ∞ω)
      (fun q : ProductSpace (InfinitePlace K) => q v) p :=
    (contDiff_apply ℝ EuclideanSpatial v).contDiffAt
  exact ContDiffAt.comp
    (f := fun q : ProductSpace (InfinitePlace K) => q v)
    (g := sourceArchEuclideanProjectiveAction (sourceKPArchProjectiveAt K hζ v a)) p ho hi

theorem sourceKPArchEuclideanAction_mul (a b : PGL(2,InfiniteAdeleRing K))
    (p : ProductSpace (InfinitePlace K)) :
    sourceKPArchEuclideanAction K hζ (a*b) p =
      sourceKPArchEuclideanAction K hζ a (sourceKPArchEuclideanAction K hζ b p) := by
  unfold sourceKPArchEuclideanAction
  rw [sourceKPArchUpperEuclideanMap_left_inverse,sourceKPArchUpperAction_mul]

theorem sourceKPArchEuclideanAction_one (p : ProductSpace (InfinitePlace K))
    (hp : p ∈ productUpper (InfinitePlace K)) : sourceKPArchEuclideanAction K hζ 1 p = p := by
  unfold sourceKPArchEuclideanAction
  rw [sourceKPArchUpperAction_one]
  exact sourceKPArchUpperEuclideanMap_right_inverse K p (fun v => hp v (Set.mem_univ v))

def sourceKPArchUpperActionHomeomorph (a : PGL(2,InfiniteAdeleRing K)) :
    SourceKPArchUpperHalfSpace K ≃ₜ SourceKPArchUpperHalfSpace K where
  toFun := sourceKPArchUpperAction K hζ a
  invFun := sourceKPArchUpperAction K hζ a⁻¹
  left_inv p := by rw [← sourceKPArchUpperAction_mul,inv_mul_cancel,sourceKPArchUpperAction_one]
  right_inv p := by rw [← sourceKPArchUpperAction_mul,mul_inv_cancel,sourceKPArchUpperAction_one]
  continuous_toFun := sourceKPArchUpperAction_continuous K hζ a
  continuous_invFun := sourceKPArchUpperAction_continuous K hζ a⁻¹

def sourceKPArchPositiveActionHomeomorph (a : PGL(2,InfiniteAdeleRing K)) :
    SourceKPArchPositiveCoordinates K ≃ₜ SourceKPArchPositiveCoordinates K :=
  (sourceKPArchPositiveHomeomorph K).symm.trans
    ((sourceKPArchUpperActionHomeomorph K hζ a).trans (sourceKPArchPositiveHomeomorph K))

theorem sourceKPArchPositiveActionHomeomorph_apply (a : PGL(2,InfiniteAdeleRing K))
    (p : SourceKPArchPositiveCoordinates K) :
    (sourceKPArchPositiveActionHomeomorph K hζ a p).val = sourceKPArchEuclideanAction K hζ a p.val := by
  change sourceKPArchUpperEuclideanMap K
      (sourceKPArchUpperAction K hζ a (sourceKPArchPositiveToUpper K p)) =
    sourceKPArchUpperEuclideanMap K
      (sourceKPArchUpperAction K hζ a (sourceKPArchEuclideanUpperMap K p.val))
  rw [sourceKPArchPositiveToUpper_eq]

end
end ArtinMatthews
