module

public import ArtinMatthews.SpectralGamma0EisensteinSignedRows


set_option backward.privateInPublic true
@[expose] public section

/-! Actual positive primitive Gamma0 rows, indexed by their positive natural first coordinate. -/
noncomputable section
namespace ArtinMatthews

abbrev Gamma0EisensteinPositiveFirst (N : ℕ) := {c : ℕ // 0<c ∧ (c:ZMod N)=0}

abbrev Gamma0EisensteinPositiveCoordinates (N : ℕ) :=
  Σ c : Gamma0EisensteinPositiveFirst N, {d : ℤ // IsCoprime (c.val:ℤ) d}

def gamma0EisensteinPositiveCoordinateRow (N : ℕ) (v : Gamma0EisensteinPositiveCoordinates N) :
    Gamma0EisensteinPositiveRows N :=
  ⟨⟨![(v.1.val:ℤ),v.2.val],⟨v.2.property,by simpa using v.1.property.2⟩⟩,by
    change 0<(v.1.val:ℤ)
    exact_mod_cast v.1.property.1⟩

def gamma0EisensteinPositiveRowCoordinate (N : ℕ) (v : Gamma0EisensteinPositiveRows N) :
    Gamma0EisensteinPositiveCoordinates N := by
  have hv : ((v.val.val 0).toNat:ℤ)=v.val.val 0 := Int.toNat_of_nonneg v.property.le
  refine ⟨⟨(v.val.val 0).toNat,?_,?_⟩,⟨v.val.val 1,?_⟩⟩
  · omega
  · rw [← Int.cast_natCast,hv]
    exact v.val.property.2
  · rw [hv]
    exact v.val.property.1

theorem gamma0EisensteinPositiveCoordinate_left_inv (N : ℕ) :
    Function.LeftInverse (gamma0EisensteinPositiveRowCoordinate N) (gamma0EisensteinPositiveCoordinateRow N) := by
  rintro ⟨⟨c,hc⟩,⟨d,hd⟩⟩
  simp [gamma0EisensteinPositiveRowCoordinate,gamma0EisensteinPositiveCoordinateRow]

theorem gamma0EisensteinPositiveCoordinate_right_inv (N : ℕ) :
    Function.RightInverse (gamma0EisensteinPositiveRowCoordinate N) (gamma0EisensteinPositiveCoordinateRow N) := by
  intro v
  apply Subtype.ext
  apply Subtype.ext
  funext i
  fin_cases i
  · simp [gamma0EisensteinPositiveRowCoordinate,gamma0EisensteinPositiveCoordinateRow,
      Int.toNat_of_nonneg v.property.le]
  · rfl

def gamma0EisensteinPositiveCoordinateEquiv (N : ℕ) :
    Gamma0EisensteinPositiveCoordinates N ≃ Gamma0EisensteinPositiveRows N where
  toFun := gamma0EisensteinPositiveCoordinateRow N
  invFun := gamma0EisensteinPositiveRowCoordinate N
  left_inv := gamma0EisensteinPositiveCoordinate_left_inv N
  right_inv := gamma0EisensteinPositiveCoordinate_right_inv N

end ArtinMatthews
