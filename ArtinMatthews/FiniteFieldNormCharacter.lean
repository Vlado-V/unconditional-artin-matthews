module

public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.GroupTheory.Coset.Card


set_option backward.privateInPublic true
@[expose] public section

/-! Actual norm and trace lifting of finite-field characters. These
construct the lifted characters and prove their exact order and additive
primitivity; no Gauss-sum lifting formula is assumed. -/
namespace ArtinMatthews.FiniteFieldCharacter
open scoped Classical
noncomputable section
variable (F E : Type*) [Field F] [Field E] [Finite E] [Algebra F E]
variable {C : Type*} [CommMonoidWithZero C]

def normLift (χ : MulChar F C) : MulChar E C where
  toMonoidHom := χ.toMonoidHom.comp (Algebra.norm F)
  map_nonunit' x hx := by
    have hx0 : x=0 := by simpa only [isUnit_iff_ne_zero,not_not] using hx
    subst x
    change χ (Algebra.norm F (0 : E)) = 0
    rw [Algebra.norm_zero,MulChar.map_zero]

theorem normLift_apply (χ : MulChar F C) (x : E) :
    normLift F E χ x = χ (Algebra.norm F x) := rfl

def normLiftHom : MulChar F C →* MulChar E C where
  toFun := normLift F E
  map_one' := by
    apply MulChar.ext
    intro x
    simp only [normLift_apply,MulChar.one_apply (x.isUnit.map (Algebra.norm F)),MulChar.one_apply_coe]
  map_mul' χ θ := by
    ext x
    simp only [normLift_apply,MulChar.mul_apply]

theorem normLift_injective : Function.Injective (normLift F E (C := C)) := by
  intro χ θ h
  apply MulChar.ext
  intro x
  obtain ⟨y,hy⟩ := FiniteField.norm_surjective F E (x : F)
  have he := congrArg (fun ψ : MulChar E C => ψ y) h
  simpa only [normLift_apply,hy] using he

theorem normLift_orderOf (χ : MulChar F C) : orderOf (normLift F E χ) = orderOf χ :=
  orderOf_injective (normLiftHom F E) (normLift_injective F E) χ

theorem normLift_pow (χ : MulChar F C) (n : ℕ) :
    normLift F E (χ^n) = normLift F E χ^n := (normLiftHom F E).map_pow χ n

theorem normLift_ne_one_iff (χ : MulChar F C) : normLift F E χ ≠ 1 ↔ χ ≠ 1 := by
  rw [← (normLiftHom F E).map_one]
  exact (normLift_injective F E).ne_iff

def traceLift (ψ : AddChar F C) : AddChar E C :=
  ψ.compAddMonoidHom (Algebra.trace F E).toAddMonoidHom

omit [Finite E] in
theorem traceLift_apply (ψ : AddChar F C) (x : E) :
    traceLift F E ψ x = ψ (Algebra.trace F E x) := rfl

theorem traceLift_injective : Function.Injective (traceLift F E (C := C)) := by
  let : Finite F := Finite.of_injective _ (algebraMap F E).injective
  exact AddChar.compAddMonoidHom_injective_left _ (Algebra.trace_surjective F E)

theorem traceLift_primitive (ψ : AddChar F C) (hψ : ψ ≠ 1) :
    (traceLift F E ψ).IsPrimitive := by
  apply AddChar.IsPrimitive.of_ne_one
  intro h
  apply hψ
  apply traceLift_injective F E
  exact h.trans (by ext x; simp only [traceLift_apply,AddChar.one_apply])

end
end ArtinMatthews.FiniteFieldCharacter
