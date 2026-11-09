module

public import ArtinMatthews.SourceGlobalArchJacquet


set_option backward.privateInPublic true
@[expose] public section

/-! The product diagonal in the actual infinite adeles and its exact local Jacquet coordinates. -/
namespace ArtinMatthews
open NumberField Matrix StandardAdelic SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPArchJacquetDiagonalUnits (y : (v : InfinitePlace K) → v.Completionˣ) :
    (InfiniteAdeleRing K)ˣ where
  val := fun v => (y v : v.Completion)
  inv := fun v => (y v).inv
  val_inv := by
    funext v
    change (y v : v.Completion)*(y v).inv = 1
    exact (y v).val_inv
  inv_val := by
    funext v
    change (y v).inv*(y v : v.Completion) = 1
    exact (y v).inv_val

def sourceKPArchJacquetDiagonal (y : (v : InfinitePlace K) → v.Completionˣ) :
    PGL(2,InfiniteAdeleRing K) :=
  sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) (sourceKPArchJacquetDiagonalUnits K y)

theorem sourceKPArchJacquetDiagonal_at (y : (v : InfinitePlace K) → v.Completionˣ)
    (v : InfinitePlace K) (hv : InfinitePlace.IsComplex v) :
    sourceArchProjectiveAt K hζ v (sourceKPArchJacquetDiagonal K y) =
      sourcePGL2Diagonal (Units.map (sourceArchCompletionEquiv K v hv).toMonoidHom (y v)) := by
  let e := (sourceKPArchComplexEquiv K hζ v).toRingHom.comp (sourceArchAdeleEval K v)
  change ProjGenLinGroup.map e (sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K)
    (sourceKPArchJacquetDiagonalUnits K y)) = _
  rw [sourceKPProjectiveDiagonalHom_map]
  have hu : Units.map e.toMonoidHom (sourceKPArchJacquetDiagonalUnits K y) =
      Units.map (sourceArchCompletionEquiv K v hv).toMonoidHom (y v) := by
    apply Units.ext
    rfl
  rw [hu]
  change ProjGenLinGroup.mk (sourceKPDiagonalHom ℂ _) = ProjGenLinGroup.mk (sourceGL2Diagonal _)
  rw [sourceKPDiagonalHom_field]

theorem sourceKPArchJacquetDiagonal_localSection (s : ℂ)
    (y : (v : InfinitePlace K) → v.Completionˣ) (v : InfinitePlace K)
    (hv : InfinitePlace.IsComplex v) (x : v.Completion) :
    sourceArchSphericalSection s
      (sourcePGL2Weyl * sourcePGL2Upper (sourceKPArchComplexEquiv K hζ v x) *
        sourceArchProjectiveAt K hζ v (sourceKPArchJacquetDiagonal K y)) =
      sourceArchCompletedSphericalSection K v hv s
        (sourcePGL2Weyl * sourcePGL2Upper x * sourcePGL2Diagonal (y v)) := by
  rw [sourceKPArchJacquetDiagonal_at K hζ y v hv,sourceArchCompletedSphericalSection_bigCell]
  rfl

theorem sourceKPLocalInfiniteCharacter_star (v : InfinitePlace K) (x : v.Completion) :
    star (localInfiniteCharacter K v x) = localInfiniteCharacter K v (-x) := by
  rw [AddChar.map_neg_eq_inv]
  have h : ‖localInfiniteCharacter K v x‖ = 1 := by
    rw [localInfiniteCharacter_single]
    exact archCharacter_unitary K _
  exact (Complex.inv_eq_conj h).symm

end
end ArtinMatthews
