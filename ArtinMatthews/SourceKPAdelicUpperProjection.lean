module

public import ArtinMatthews.SourceKPAdelicUpper
public import ArtinMatthews.SourceKPAdelicRationalSum


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

theorem sourceKPUpperMatrix_projective_injective (R : Type*) [CommRing R] :
    Function.Injective (fun x : R => ProjGenLinGroup.mk (sourceKPUpperMatrix R x)) := by
  intro x y h
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h11 := congrArg (fun g : GL (Fin 2) R => g 1 1) hu
  have hunit : u = 1 := by
    apply Units.ext
    simpa [sourceKPMatrix_right_scalar_entry, sourceKPUpperMatrix] using h11
  rw [hunit, map_one, mul_one] at hu
  have h01 := congrArg (fun g : GL (Fin 2) R => g 0 1) hu
  exact h01

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicUpperHom : Multiplicative 𝔸[K] →* SourceKPAdelicProjective K hζ where
  toFun x := sourceKPAdelicUpperLift K hζ x.toAdd
  map_one' := sourceKPAdelicUpperLift_zero K hζ
  map_mul' x y := sourceKPAdelicUpperLift_add K hζ x.toAdd y.toAdd

theorem sourceKPAdelicUpperLift_projection (x : 𝔸[K]) :
    sourceKPAdelicProjectiveProjection K hζ (sourceKPAdelicUpperLift K hζ x) =
      ProjGenLinGroup.mk (sourceKPUpperMatrix 𝔸[K] x) := by
  apply (sourceKPAdelicProjectiveProductEquiv K).injective
  rw [sourceKPAdelicProjectiveProjection_product]
  change (ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) x.1),
    ProjGenLinGroup.mk (sourceKPUpperMatrix 𝔸ᶠ[K] x.2)) =
    (ProjGenLinGroup.mk (GeneralLinearGroup.map (sourceKPAdeleInfiniteProjection K)
      (sourceKPUpperMatrix 𝔸[K] x)),
      ProjGenLinGroup.mk (GeneralLinearGroup.map (sourceKPAdeleFiniteProjection K)
      (sourceKPUpperMatrix 𝔸[K] x)))
  apply Prod.ext
  · exact (congrArg (ProjGenLinGroup.mk (n := Fin 2) (R := InfiniteAdeleRing K))
      (sourceKPUpperMatrix_map (sourceKPAdeleInfiniteProjection K) x)).symm
  · exact (congrArg (ProjGenLinGroup.mk (n := Fin 2) (R := 𝔸ᶠ[K]))
      (sourceKPUpperMatrix_map (sourceKPAdeleFiniteProjection K) x)).symm

theorem sourceKPAdelicUpperLift_injective : Function.Injective (sourceKPAdelicUpperLift K hζ) := by
  intro x y h
  apply sourceKPUpperMatrix_projective_injective 𝔸[K]
  change ProjGenLinGroup.mk (sourceKPUpperMatrix 𝔸[K] x) =
    ProjGenLinGroup.mk (sourceKPUpperMatrix 𝔸[K] y)
  rw [← sourceKPAdelicUpperLift_projection K hζ x, ← sourceKPAdelicUpperLift_projection K hζ y, h]

theorem sourceKPAdelicRationalSum_canonical_bruhat
    (f : SourceKPRationalBorelFunction K hζ) (g : SourceKPAdelicProjective K hζ)
    (hs : Summable (sourceKPAdelicRationalSummand K hζ f g)) :
    sourceKPAdelicRationalSum K hζ f g = f.val g +
      ∑' x : K, f.val (sourceKPAdelicProjectiveWeyl K hζ *
        sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x) * g) := by
  simp_rw [sourceKPAdelicUpperLift_rational]
  exact sourceKPAdelicRationalSum_bruhat K hζ f g hs

end
end ArtinMatthews
