module

public import ArtinMatthews.SpectralCuspEisensteinResidueRows


set_option backward.privateInPublic true
@[expose] public section

/-! Exact positive-row coordinates for every pair of actual cusps. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace ArtinMatthews

abbrev CuspEisensteinPositiveCoordinates (N : ℕ) (r a : SL(2,ℤ)) :=
  Σ c : {c : ℕ // 0 < c}, CuspEisensteinRowFibre N r a c.val

def cuspEisensteinPositiveCoordinateRow (N : ℕ) (r a : SL(2,ℤ))
    (v : CuspEisensteinPositiveCoordinates N r a) : CuspEisensteinPositiveRows N r a :=
  ⟨⟨![(v.1.val:ℤ),v.2.val],v.2.property⟩,by
    change 0 < (v.1.val:ℤ)
    exact_mod_cast v.1.property⟩

def cuspEisensteinPositiveRowCoordinate (N : ℕ) (r a : SL(2,ℤ))
    (v : CuspEisensteinPositiveRows N r a) : CuspEisensteinPositiveCoordinates N r a := by
  have hv : ((v.val.val 0).toNat:ℤ)=v.val.val 0 := Int.toNat_of_nonneg v.property.le
  refine ⟨⟨(v.val.val 0).toNat,by omega⟩,⟨v.val.val 1,?_⟩⟩
  have he : ![(((v.val.val 0).toNat):ℤ),v.val.val 1]=v.val.val := by
    funext i
    fin_cases i
    · exact hv
    · rfl
  rw [he]
  exact v.val.property

def cuspEisensteinPositiveCoordinateEquiv (N : ℕ) (r a : SL(2,ℤ)) :
    CuspEisensteinPositiveCoordinates N r a ≃ CuspEisensteinPositiveRows N r a where
  toFun := cuspEisensteinPositiveCoordinateRow N r a
  invFun := cuspEisensteinPositiveRowCoordinate N r a
  left_inv v := by
    rcases v with ⟨⟨c,hc⟩,⟨d,hd⟩⟩
    simp [cuspEisensteinPositiveRowCoordinate,cuspEisensteinPositiveCoordinateRow]
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i
    · simp [cuspEisensteinPositiveRowCoordinate,cuspEisensteinPositiveCoordinateRow,
        Int.toNat_of_nonneg v.property.le]
    · rfl

end ArtinMatthews
