module

public import ArtinMatthews.SourceKPAdelicCompactSection
public import ArtinMatthews.SourceKPAdelicTorusWeyl


set_option backward.privateInPublic true
@[expose] public section

/-! Torus coordinates of the actual compact section and their exact
conversion to the scalar intertwining kernel by adelic dilation. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCompactSection_coordinate (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) :
    ((sourceKPAdelicCompactSection K hζ s).val g).val t =
      (sourceKPAdelicBorelModularHalf K hζ (sourceKPAdelicBorelTorusInclusion K hζ t))⁻¹ *
        sourceKPAdelicCompactScalar K hζ s (t.val * g) := by
  have hd : sourceKPAdelicBorelModularHalf K hζ
      (sourceKPAdelicBorelTorusInclusion K hζ t) ≠ 0 := by
    change (sourceKPIdeleComplexNorm K (1/2 : ℂ)
      (sourceKPAdelicTorusIdele K hζ
        (sourceKPAdelicBorelTorusProjection K hζ (sourceKPAdelicBorelTorusInclusion K hζ t))) : ℂ) ≠ 0
    exact Units.ne_zero _
  have hc := sourceAlgebraicInducedSpace_covariant
    (sourceKPAdelicCoveringBorel K hζ) (sourceKPAdelicNormalizedBorelRepresentation K hζ s)
    (sourceKPAdelicCompactSection K hζ s) (sourceKPAdelicBorelTorusInclusion K hζ t) g
  have hv := congrArg (fun v : SourceKPAdelicTorusInducedSpace K hζ s => v.val 1) hc
  change sourceKPAdelicCompactScalar K hζ s (t.val*g) =
    sourceKPAdelicBorelModularHalf K hζ (sourceKPAdelicBorelTorusInclusion K hζ t) *
      ((sourceKPAdelicCompactSection K hζ s).val g).val
        (1 * sourceKPAdelicBorelTorusProjection K hζ (sourceKPAdelicBorelTorusInclusion K hζ t)) at hv
  rw [sourceKPAdelicBorelTorusProjection_inclusion, one_mul] at hv
  rw [hv, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

theorem sourceKPAdelicTorus_left_weyl (t : sourceKPAdelicCoveringTorus K hζ) :
    t.val * sourceKPAdelicProjectiveWeyl K hζ =
      sourceKPAdelicProjectiveWeyl K hζ * (sourceKPAdelicCoveringTorusWeyl K hζ t).val := by
  let W := sourceKPAdelicProjectiveWeyl K hζ
  have hW : W*W = 1 := sourceKPAdelicProjectiveWeyl_square K hζ
  have hi : W⁻¹ = W := inv_eq_of_mul_eq_one_right hW
  change t.val * W = W * (W * t.val * W⁻¹)
  rw [hi]
  calc
    t.val * W = (W*W) * t.val * W := by rw [hW, one_mul]
    _ = W * (W * t.val * W) := by group

def sourceKPAdelicCoordinateKernel (s : ℂ) (g : SourceKPAdelicProjective K hζ)
    (t : sourceKPAdelicCoveringTorus K hζ) (y : 𝔸[K]) : ℂ :=
  ((sourceKPAdelicCompactSection K hζ s).val
    (sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ y * g)).val t

theorem sourceKPAdelicCoordinateKernel_eq_scalar (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) (y : 𝔸[K]) :
    sourceKPAdelicCoordinateKernel K hζ s g t y =
      (sourceKPAdelicBorelModularHalf K hζ (sourceKPAdelicBorelTorusInclusion K hζ t))⁻¹ *
        sourceKPAdelicCompactScalar K hζ s
          (sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ
            ((sourceKPAdelicTorusIdele K hζ (sourceKPAdelicCoveringTorusWeyl K hζ t) : 𝔸[K]) * y) *
              ((sourceKPAdelicCoveringTorusWeyl K hζ t).val * g)) := by
  unfold sourceKPAdelicCoordinateKernel
  rw [sourceKPAdelicCompactSection_coordinate]
  congr 2
  calc
    t.val * (sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ y * g) =
        (t.val * sourceKPAdelicProjectiveWeyl K hζ) * sourceKPAdelicUpperLift K hζ y * g := by group
    _ = (sourceKPAdelicProjectiveWeyl K hζ * (sourceKPAdelicCoveringTorusWeyl K hζ t).val) *
        sourceKPAdelicUpperLift K hζ y * g := by rw [sourceKPAdelicTorus_left_weyl]
    _ = sourceKPAdelicProjectiveWeyl K hζ *
        ((sourceKPAdelicCoveringTorusWeyl K hζ t).val * sourceKPAdelicUpperLift K hζ y) * g := by group
    _ = _ := by rw [sourceKPAdelicTorus_upper]; group

end
end ArtinMatthews
