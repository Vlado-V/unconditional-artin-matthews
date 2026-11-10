module

public import ArtinMatthews.SpectralGamma0EisensteinPrimitiveRows


set_option backward.privateInPublic true
@[expose] public section

/-! A literal accounting of the two signs and the two zero-first-coordinate rows. -/
noncomputable section
open Set
namespace ArtinMatthews

def gamma0EisensteinNegPrimitiveRow (N : ℕ) (v : Gamma0EisensteinPrimitiveRows N) :
    Gamma0EisensteinPrimitiveRows N :=
  ⟨-v.val,⟨v.property.1.neg_neg,by simpa using congrArg Neg.neg v.property.2⟩⟩

@[simp] theorem gamma0EisensteinNegPrimitiveRow_involutive (N : ℕ)
    (v : Gamma0EisensteinPrimitiveRows N) :
    gamma0EisensteinNegPrimitiveRow N (gamma0EisensteinNegPrimitiveRow N v)=v := by
  apply Subtype.ext
  exact neg_neg v.val

def gamma0EisensteinZeroPrimitiveRow (N : ℕ) (b : Bool) : Gamma0EisensteinPrimitiveRows N :=
  ⟨![0,if b then 1 else -1],by cases b <;> simp [isCoprime_zero_left]⟩

abbrev Gamma0EisensteinPositiveRows (N : ℕ) :=
  {v : Gamma0EisensteinPrimitiveRows N // 0<v.val 0}

abbrev Gamma0EisensteinSignedRowIndex (N : ℕ) :=
  Bool ⊕ (Gamma0EisensteinPositiveRows N × Bool)

def gamma0EisensteinSignedRow (N : ℕ) : Gamma0EisensteinSignedRowIndex N → Gamma0EisensteinPrimitiveRows N
  | .inl b => gamma0EisensteinZeroPrimitiveRow N b
  | .inr (v,b) => if b then v.val else gamma0EisensteinNegPrimitiveRow N v.val

def gamma0EisensteinSignedRowInverse (N : ℕ) (v : Gamma0EisensteinPrimitiveRows N) :
    Gamma0EisensteinSignedRowIndex N :=
  if h0 : v.val 0=0 then .inl (decide (v.val 1=1))
  else if hp : 0<v.val 0 then .inr (⟨v,hp⟩,true)
  else .inr (⟨gamma0EisensteinNegPrimitiveRow N v,by
    change 0< -v.val 0
    omega⟩,false)

theorem gamma0EisensteinSignedRow_left_inv (N : ℕ) :
    Function.LeftInverse (gamma0EisensteinSignedRowInverse N) (gamma0EisensteinSignedRow N) := by
  intro i
  rcases i with b | ⟨v,b⟩
  · cases b <;> simp [gamma0EisensteinSignedRow,gamma0EisensteinZeroPrimitiveRow,
      gamma0EisensteinSignedRowInverse]
  · cases b
    · simp [gamma0EisensteinSignedRow,gamma0EisensteinSignedRowInverse,
        gamma0EisensteinNegPrimitiveRow,v.property.ne',v.property.le]
    · simp [gamma0EisensteinSignedRow,gamma0EisensteinSignedRowInverse,v.property.ne',v.property]

theorem gamma0EisensteinSignedRow_right_inv (N : ℕ) :
    Function.RightInverse (gamma0EisensteinSignedRowInverse N) (gamma0EisensteinSignedRow N) := by
  intro v
  by_cases h0 : v.val 0=0
  · have hu : v.val 1=1 ∨ v.val 1= -1 := by
      apply Int.isUnit_iff.mp
      exact isCoprime_zero_left.mp (h0 ▸ v.property.1)
    rcases hu with hu | hu
    · simp [gamma0EisensteinSignedRowInverse,h0,hu,gamma0EisensteinSignedRow]
      apply Subtype.ext
      funext i
      fin_cases i <;> simp [gamma0EisensteinZeroPrimitiveRow,h0,hu]
    · simp [gamma0EisensteinSignedRowInverse,h0,hu,gamma0EisensteinSignedRow]
      apply Subtype.ext
      funext i
      fin_cases i <;> simp [gamma0EisensteinZeroPrimitiveRow,h0,hu]
  · by_cases hp : 0<v.val 0
    · simp [gamma0EisensteinSignedRowInverse,h0,hp,gamma0EisensteinSignedRow]
    · simp [gamma0EisensteinSignedRowInverse,h0,hp,gamma0EisensteinSignedRow]

def gamma0EisensteinSignedRowEquiv (N : ℕ) :
    Gamma0EisensteinSignedRowIndex N ≃ Gamma0EisensteinPrimitiveRows N where
  toFun := gamma0EisensteinSignedRow N
  invFun := gamma0EisensteinSignedRowInverse N
  left_inv := gamma0EisensteinSignedRow_left_inv N
  right_inv := gamma0EisensteinSignedRow_right_inv N

end ArtinMatthews
