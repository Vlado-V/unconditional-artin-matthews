module

public import ArtinMatthews.MarkedPhysicalRawEndpoint
public import ArtinMatthews.MarkedFiniteMatrixSupport


set_option backward.privateInPublic true
@[expose] public section

/-! The literal uniform slot-permutation matrix on physical states.
Every ordered list is retained, with no quotient by permutations. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical
noncomputable section

def markedPhysicalSlotEquiv {J : Type*}
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ))
    (σ : J → Equiv.Perm (Fin M)) :
    MarkedPhysicalState P M Z ≃ MarkedPhysicalState P M Z where
  toFun s := ⟨(s.1.1,fun j k => s.1.2 j (σ j k)),
    (markedPhysicalStateCondition_slots _ _ σ).mpr s.2⟩
  invFun s := ⟨(s.1.1,fun j k => s.1.2 j ((σ j).symm k)),
    (markedPhysicalStateCondition_slots _ _ (fun j => (σ j).symm)).mpr s.2⟩
  left_inv s := by
    apply Subtype.ext
    change (s.1.1,fun j k => s.1.2 j (σ j ((σ j).symm k)))=s.1
    apply Prod.ext
    · rfl
    · funext j k
      simp
  right_inv s := by
    apply Subtype.ext
    change (s.1.1,fun j k => s.1.2 j ((σ j).symm (σ j k)))=s.1
    apply Prod.ext
    · rfl
    · funext j k
      simp

@[simp] theorem markedPhysicalSlotEquiv_position {J : Type*}
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ))
    (σ : J → Equiv.Perm (Fin M)) (s : MarkedPhysicalState P M Z) :
    (markedPhysicalSlotEquiv P M Z σ s).1.1=s.1.1 := rfl

def markedPhysicalSlotMatrix {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) :
    Matrix (MarkedPhysicalState P M Z) (MarkedPhysicalState P M Z) ℂ := fun s t =>
  (Fintype.card (J → Equiv.Perm (Fin M)) : ℂ)⁻¹ *
    ∑ σ : J → Equiv.Perm (Fin M), if t=markedPhysicalSlotEquiv P M Z σ s then 1 else 0

theorem markedPhysicalSlotMatrix_action {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ))
    (f : MarkedPhysicalState P M Z → ℂ) (s : MarkedPhysicalState P M Z) :
    (markedPhysicalSlotMatrix P M Z *ᵥ f) s =
      (Fintype.card (J → Equiv.Perm (Fin M)) : ℂ)⁻¹ *
        ∑ σ : J → Equiv.Perm (Fin M), f (markedPhysicalSlotEquiv P M Z σ s) := by
  simp only [Matrix.mulVec,dotProduct,markedPhysicalSlotMatrix,mul_assoc,
    Finset.sum_mul,← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  simp

theorem markedPhysicalSlotMatrix_fixes {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ))
    (f : MarkedPhysicalState P M Z → ℂ)
    (hf : ∀ σ s, f (markedPhysicalSlotEquiv P M Z σ s)=f s) :
    markedPhysicalSlotMatrix P M Z *ᵥ f=f := by
  funext s
  rw [markedPhysicalSlotMatrix_action]
  simp only [hf,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hN : (Fintype.card (J → Equiv.Perm (Fin M)) : ℂ)≠0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact inv_mul_cancel_left₀ hN (f s)

theorem markedPhysicalSlotMatrix_preserves_position {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ))
    (s t : MarkedPhysicalState P M Z) (h : markedPhysicalSlotMatrix P M Z s t≠0) :
    s.1.1=t.1.1 := by
  by_contra hn
  apply h
  unfold markedPhysicalSlotMatrix
  suffices (∑ σ : J → Equiv.Perm (Fin M),
      if t=markedPhysicalSlotEquiv P M Z σ s then (1:ℂ) else 0)=0 by rw [this,mul_zero]
  apply Finset.sum_eq_zero
  intro σ _
  have he : t≠markedPhysicalSlotEquiv P M Z σ s := by
    intro he
    exact hn (congrArg (fun u : MarkedPhysicalState P M Z => u.1.1) he).symm
  exact ite_eq_right he

theorem markedPhysicalSlotMatrix_isHermitian {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) :
    (markedPhysicalSlotMatrix P M Z).IsHermitian := by
  ext s t
  simp only [Matrix.conjTranspose_apply,markedPhysicalSlotMatrix,star_mul,star_inv₀,star_natCast]
  rw [mul_comm]
  apply congrArg (fun z : ℂ => (Fintype.card (J → Equiv.Perm (Fin M)) : ℂ)⁻¹*z)
  simp only [star_sum,apply_ite star,star_one,star_zero]
  have hi := Equiv.sum_comp (Equiv.inv (J → Equiv.Perm (Fin M)))
    (fun σ => if s=markedPhysicalSlotEquiv P M Z σ t then (1:ℂ) else 0)
  rw [← hi]
  apply Finset.sum_congr rfl
  intro σ _
  have he : s=markedPhysicalSlotEquiv P M Z σ⁻¹ t ↔
      t=markedPhysicalSlotEquiv P M Z σ s := by
    change s=(markedPhysicalSlotEquiv P M Z σ).symm t ↔ _
    constructor
    · intro h
      simpa only [Equiv.apply_symm_apply] using
        (congrArg (markedPhysicalSlotEquiv P M Z σ) h).symm
    · intro h
      simpa only [Equiv.symm_apply_apply] using
        (congrArg (markedPhysicalSlotEquiv P M Z σ).symm h).symm
  simp only [Equiv.inv_apply,he]

end
end ArtinMatthews
