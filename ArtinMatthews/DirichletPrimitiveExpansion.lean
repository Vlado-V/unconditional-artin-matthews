module

public import ArtinMatthews.IdealPrimitiveCharacters


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {r Q : ℕ} [NeZero r]

def dirichletPrimitiveRepresentative (hQr : r ≤ Q)
    (χ : DirichletCharacter ℂ r) : IdealPrimitiveCharacters Q :=
  ⟨⟨χ.conductor, Finset.mem_Icc.mpr
    ⟨Nat.pos_of_ne_zero χ.conductor_ne_zero,
      (Nat.le_of_dvd (NeZero.pos r) χ.conductor_dvd_level).trans hQr⟩⟩,
    ⟨χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive⟩⟩

theorem dirichletPrimitiveRepresentative_value (hQr : r ≤ Q)
    (χ : DirichletCharacter ℂ r) (n : ℕ) (hn : n.Coprime r) :
    idealPrimitiveCharacterValue (dirichletPrimitiveRepresentative hQr χ) n =
      χ (n : ZMod r) := by
  change χ.primitiveCharacter (n : ZMod χ.conductor) = χ (n : ZMod r)
  simpa only [Int.cast_natCast] using
    χ.primitiveCharacter_apply_of_isCoprime hn.isCoprime

theorem dirichletPrimitiveRepresentative_injective (hQr : r ≤ Q) :
    Function.Injective (dirichletPrimitiveRepresentative hQr) := by
  intro χ ψ h
  apply MulChar.ext
  intro a
  have hv := congrArg
    (fun p => idealPrimitiveCharacterValue p (a : ZMod r).val) h
  rw [dirichletPrimitiveRepresentative_value hQr χ _ (ZMod.val_coe_unit_coprime a),
    dirichletPrimitiveRepresentative_value hQr ψ _ (ZMod.val_coe_unit_coprime a)] at hv
  simpa only [ZMod.natCast_zmod_val] using hv

def dirichletPrimitiveCoefficient (hQr : r ≤ Q)
    (a : DirichletCharacter ℂ r → ℂ) (ψ : IdealPrimitiveCharacters Q) : ℂ :=
  ∑ χ : DirichletCharacter ℂ r,
    if dirichletPrimitiveRepresentative hQr χ = ψ then a χ else 0

theorem dirichletPrimitiveCoefficient_sum (hQr : r ≤ Q)
    (a : DirichletCharacter ℂ r → ℂ) (f : IdealPrimitiveCharacters Q → ℂ) :
    (∑ ψ : IdealPrimitiveCharacters Q, dirichletPrimitiveCoefficient hQr a ψ * f ψ) =
      ∑ χ : DirichletCharacter ℂ r, a χ * f (dirichletPrimitiveRepresentative hQr χ) := by
  classical
  simp only [dirichletPrimitiveCoefficient, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  simp

theorem dirichletPrimitiveCoefficient_l1_le (hQr : r ≤ Q)
    (a : DirichletCharacter ℂ r → ℂ) :
    (∑ ψ : IdealPrimitiveCharacters Q, ‖dirichletPrimitiveCoefficient hQr a ψ‖) ≤
      ∑ χ : DirichletCharacter ℂ r, ‖a χ‖ := by
  classical
  calc
    _ ≤ ∑ ψ : IdealPrimitiveCharacters Q, ∑ χ : DirichletCharacter ℂ r,
        if dirichletPrimitiveRepresentative hQr χ = ψ then ‖a χ‖ else 0 := by
      apply Finset.sum_le_sum
      intro ψ _
      unfold dirichletPrimitiveCoefficient
      simpa only [apply_ite norm, norm_zero] using norm_sum_le
        (s := Finset.univ)
        (f := fun χ => if dirichletPrimitiveRepresentative hQr χ = ψ then a χ else 0)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      simp

end
end ArtinMatthews
