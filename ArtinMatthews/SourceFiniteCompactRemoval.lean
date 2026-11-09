module

public import ArtinMatthews.SourceFiniteProjectiveSupport
public import ArtinMatthews.SourceKPLocalRestBase
public import ArtinMatthews.SourceKPTameCompactEmbedding


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (h6 : (6 : 𝓞 K) ∉ P.asIdeal)

def sourceKPFiniteCompactRemove (g : SourceKPFiniteAdeleProjective K hζ)
    (k : SourceFiniteKP2Integral K P) : SourceKPAdelicProjective K hζ :=
  (1, g) * (sourceKPAdelicLocalProjective K hζ P
    (sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k))⁻¹

theorem sourceKPFiniteCompactRemove_arch (g : SourceKPFiniteAdeleProjective K hζ)
    (k : SourceFiniteKP2Integral K P) :
    (sourceKPFiniteCompactRemove K hζ P h6 g k).1 = 1 := by
  change (1 : PGL(2, InfiniteAdeleRing K)) * 1⁻¹ = 1
  simp

theorem sourceKPFiniteCompactRemove_eq_pair (g : SourceKPFiniteAdeleProjective K hζ)
    (k : SourceFiniteKP2Integral K P) :
    sourceKPFiniteCompactRemove K hζ P h6 g k =
      (1, (sourceKPFiniteCompactRemove K hζ P h6 g k).2) :=
  Prod.ext (sourceKPFiniteCompactRemove_arch K hζ P h6 g k) rfl

theorem sourceKPFiniteCompactRemove_restore (g : SourceKPFiniteAdeleProjective K hζ)
    (k : SourceFiniteKP2Integral K P) :
    sourceKPFiniteCompactRemove K hζ P h6 g k * sourceKPAdelicLocalProjective K hζ P
      (sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k) = (1, g) := by
  unfold sourceKPFiniteCompactRemove
  exact inv_mul_cancel_right _ _

theorem sourceKPAdelicLocalBase_finite_representative (a : SourceKPFiniteAdeleCover K hζ) :
    sourceKPAdelicLocalBase K hζ P (1, sourceKPFiniteAdeleProjectiveMk K hζ a) =
      ProjGenLinGroup.mk (sourceKPAdeleMatrixAt K P a.base) := by
  change ProjGenLinGroup.map (sourceKPAdeleEval K P) (ProjGenLinGroup.mk a.base) = _
  rw [ProjGenLinGroup.map_mk]
  rfl

theorem sourceKPFiniteCompactRemove_base (a : SourceKPFiniteAdeleCover K hζ)
    (k : SourceFiniteKP2Integral K P) (hk : k.val = sourceKPAdeleMatrixAt K P a.base) :
    sourceKPAdelicLocalBase K hζ P
      (sourceKPFiniteCompactRemove K hζ P h6 (sourceKPFiniteAdeleProjectiveMk K hζ a) k) = 1 := by
  rw [sourceKPFiniteCompactRemove, map_mul, map_inv,
    sourceKPAdelicLocalBase_finite_representative, sourceKPAdelicLocalBase_local]
  change ProjGenLinGroup.mk (sourceKPAdeleMatrixAt K P a.base) *
    (ProjGenLinGroup.mk k.val)⁻¹ = 1
  rw [← hk, mul_inv_cancel]

theorem sourceKPFiniteCompactRemove_scalar (s : ℂ) (g : SourceKPFiniteAdeleProjective K hζ)
    (k : SourceFiniteKP2Integral K P) (z : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCompactScalar K hζ s (z * (1, g)) =
      sourceKPAdelicCompactScalar K hζ s (z * sourceKPFiniteCompactRemove K hζ P h6 g k) := by
  have h := congrArg (fun v : SourceKPAdelicTorusInducedSpace K hζ s => v.val 1)
    (sourceKPAdelicCompactSection_right_local K hζ P h6 s
      (z * sourceKPFiniteCompactRemove K hζ P h6 g k) k)
  change sourceKPAdelicCompactScalar K hζ s
      ((z * sourceKPFiniteCompactRemove K hζ P h6 g k) *
        sourceKPAdelicLocalProjective K hζ P
          (sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k)) =
    sourceKPAdelicCompactScalar K hζ s (z * sourceKPFiniteCompactRemove K hζ P h6 g k) at h
  rw [mul_assoc, sourceKPFiniteCompactRemove_restore] at h
  exact h

theorem sourceKPFiniteCompactRemove_kernel (s : ℂ) (g : SourceKPFiniteAdeleProjective K hζ)
    (k : SourceFiniteKP2Integral K P) (x : 𝔸ᶠ[K]) :
    sourceKPFiniteIntertwiningKernel K hζ s g x =
      sourceKPFiniteIntertwiningKernel K hζ s (sourceKPFiniteCompactRemove K hζ P h6 g k).2 x := by
  have h := sourceKPFiniteCompactRemove_scalar K hζ P h6 s g k
    (1, (sourceKPAdelicProjectiveWeyl K hζ).2 * sourceKPFiniteAdeleUpperLift K hζ x)
  rw [sourceKPFiniteCompactRemove_eq_pair] at h
  simpa only [sourceKPFiniteIntertwiningKernel, Prod.mk_mul_mk, one_mul] using h

theorem sourceKPFiniteCompactRemove_coordinate_kernel (s : ℂ)
    (g t : SourceKPFiniteAdeleProjective K hζ) (k : SourceFiniteKP2Integral K P) (x : 𝔸ᶠ[K]) :
    sourceKPFiniteCoordinateIntertwiningKernel K hζ s g t x =
      sourceKPFiniteCoordinateIntertwiningKernel K hζ s
        (sourceKPFiniteCompactRemove K hζ P h6 g k).2 t x := by
  have h := sourceKPFiniteCompactRemove_scalar K hζ P h6 s g k
    (1, t * ((sourceKPAdelicProjectiveWeyl K hζ).2 * sourceKPFiniteAdeleUpperLift K hζ x))
  rw [sourceKPFiniteCompactRemove_eq_pair] at h
  simpa only [sourceKPFiniteCoordinateIntertwiningKernel, Prod.mk_mul_mk, one_mul, mul_assoc] using h

end
end ArtinMatthews
