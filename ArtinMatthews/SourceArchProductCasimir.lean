module

public import ArtinMatthews.SourceArchCoordinateCasimir


set_option backward.privateInPublic true
@[expose] public section

/-! The sum of the existing local coordinate Laplacians on an independent product. -/
namespace ArtinMatthews.SourceArchJacquet
open OAI.CubicEisenstein
open scoped BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sourceArchCoordinateProduct (s : ℂ) (p : ι → EuclideanSpatial) : ℂ :=
  ∏ v, sourceArchCoordinateProfile s (p v)

def sourceArchProductCoordinateLaplacian
    (f : (ι → EuclideanSpatial) → ℂ) (p : ι → EuclideanSpatial) : ℂ :=
  ∑ v, positiveEuclideanLaplacian (fun q => f (Function.update p v q)) (p v)

theorem sourceArchCoordinateProduct_update (s : ℂ) (p : ι → EuclideanSpatial)
    (v : ι) (q : EuclideanSpatial) :
    sourceArchCoordinateProduct s (Function.update p v q) =
      sourceArchCoordinateProfile s q *
        ∏ w ∈ Finset.univ \ {v}, sourceArchCoordinateProfile s (p w) := by
  have hfun : (fun w => sourceArchCoordinateProfile s (Function.update p v q w)) =
      Function.update (fun w => sourceArchCoordinateProfile s (p w)) v
        (sourceArchCoordinateProfile s q) := by
    funext w
    by_cases hw : w = v <;> simp [hw]
  unfold sourceArchCoordinateProduct
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ v)]

theorem sourceArchCoordinateProduct_laplacian (s c : ℂ) (p : ι → EuclideanSpatial)
    (hp : ∀ v, 0 < p v 2) :
    sourceArchProductCoordinateLaplacian (fun q => c * sourceArchCoordinateProduct s q) p =
      (Fintype.card ι : ℂ) * (1 - 4 * s ^ 2) * (c * sourceArchCoordinateProduct s p) := by
  have hterm (v : ι) : positiveEuclideanLaplacian
      (fun q => c * sourceArchCoordinateProduct s (Function.update p v q)) (p v) =
      (1 - 4 * s ^ 2) * (c * sourceArchCoordinateProduct s p) := by
    let C := ∏ w ∈ Finset.univ \ {v}, sourceArchCoordinateProfile s (p w)
    have hslice : (fun q => c * sourceArchCoordinateProduct s (Function.update p v q)) =
        (fun q => (c * C) * sourceArchCoordinateProfile s q) := by
      funext q
      rw [sourceArchCoordinateProduct_update]
      dsimp [C]
      ring
    have hvalue : sourceArchCoordinateProduct s p = sourceArchCoordinateProfile s (p v) * C := by
      simpa only [Function.update_eq_self] using sourceArchCoordinateProduct_update s p v (p v)
    rw [hslice, sourceArchCoordinateProfile_laplacian s (c * C) (p v) (hp v), hvalue]
    ring
  unfold sourceArchProductCoordinateLaplacian
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end
end ArtinMatthews.SourceArchJacquet
