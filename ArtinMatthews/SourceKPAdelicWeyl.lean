module

public import ArtinMatthews.SourceKPFiniteAdeleWeyl
public import ArtinMatthews.SourceKPAdelicCubeTorus


set_option backward.privateInPublic true
@[expose] public section

/-! Exact Weyl conjugation in the actual full adelic projective cubic
cover. The rational Weyl lift is an involution and inverts every
normalized diagonal without introducing a central factor. -/

namespace ArtinMatthews
open NumberField Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicProjectiveWeyl : SourceKPAdelicProjective K hζ :=
  sourceKPAdelicProjectiveRationalLift K hζ (ProjGenLinGroup.mk (sourceKPWeylMatrix K))

theorem sourceKPAdelicProjectiveWeyl_square :
    sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicProjectiveWeyl K hζ = 1 := by
  unfold sourceKPAdelicProjectiveWeyl
  rw [← map_mul (sourceKPAdelicProjectiveRationalLift K hζ),
    ← map_mul (ProjGenLinGroup.mk (n := Fin 2) (R := K)), sourceKPWeylMatrix_square, map_one, map_one]

theorem sourceKPAdelicProjectiveWeyl_diagonal (u : IdeleGroup (𝓞 K) K) :
    sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicProjectiveDiagonalLift K hζ u =
      sourceKPAdelicProjectiveDiagonalLift K hζ u⁻¹ * sourceKPAdelicProjectiveWeyl K hζ := by
  apply Prod.ext
  · let R := InfiniteAdeleRing K
    let m := ProjGenLinGroup.mk (n := Fin 2) (R := R)
    let v := sourceKPIdeleInfiniteUnit K u
    change m (GeneralLinearGroup.map (algebraMap K R) (sourceKPWeylMatrix K)) * m (sourceKPDiagonalHom R v) =
      m (sourceKPDiagonalHom R (sourceKPIdeleInfiniteUnit K u⁻¹)) *
        m (GeneralLinearGroup.map (algebraMap K R) (sourceKPWeylMatrix K))
    rw [sourceKPWeylMatrix_map, map_inv (sourceKPIdeleInfiniteUnit K), ← map_mul m,
      sourceKPWeylMatrix_mul_diagonal, map_mul m, ProjGenLinGroup.mk_scalar, mul_one, map_mul m]
  · change sourceKPFiniteAdeleProjectiveRationalLift K hζ (ProjGenLinGroup.mk (sourceKPWeylMatrix K)) *
      sourceKPFiniteAdeleProjectiveDiagonalLift K hζ (sourceKPIdeleFiniteUnit K u) =
      sourceKPFiniteAdeleProjectiveDiagonalLift K hζ (sourceKPIdeleFiniteUnit K u⁻¹) *
        sourceKPFiniteAdeleProjectiveRationalLift K hζ (ProjGenLinGroup.mk (sourceKPWeylMatrix K))
    rw [sourceKPFiniteAdeleProjectiveRationalLift_weyl, map_inv (sourceKPIdeleFiniteUnit K)]
    exact sourceKPFiniteAdeleProjectiveLift_weyl_diagonal K hζ _

theorem sourceKPAdelicProjectiveWeyl_conj_diagonal (u : IdeleGroup (𝓞 K) K) :
    sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicProjectiveDiagonalLift K hζ u *
      (sourceKPAdelicProjectiveWeyl K hζ)⁻¹ = sourceKPAdelicProjectiveDiagonalLift K hζ u⁻¹ := by
  rw [sourceKPAdelicProjectiveWeyl_diagonal, mul_inv_cancel_right]

end
end ArtinMatthews
