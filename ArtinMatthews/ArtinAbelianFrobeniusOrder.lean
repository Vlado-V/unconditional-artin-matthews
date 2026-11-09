module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.RingTheory.Frobenius
public import Mathlib.NumberTheory.RamificationInertia.Galois


set_option backward.privateInPublic true
@[expose] public section

/-! The order of actual arithmetic Frobenius modulo inertia is the actual
residue degree, including ramified primes. -/

noncomputable section
namespace ArtinMatthews.AbelianLocal
open scoped NumberField IsMulCommutative
attribute [local instance] Ideal.Quotient.field

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [IsAbelianGalois F E]

lemma isArithFrobAt_restrict_pow_mk
    (Q : Ideal (𝓞 E)) (σ : E ≃ₐ[F] E) (H : IsArithFrobAt (𝓞 F) σ Q)
    (n : ℕ) (x : 𝓞 E) :
    Ideal.Quotient.mk Q ((σ ^ n) • x) =
      (H.restrict ^ n) (Ideal.Quotient.mk Q x) := by
  induction n with
  | zero => simp only [pow_zero, one_smul, AlgHom.one_apply]
  | succ n ih =>
    rw [pow_succ', mul_smul]
    change Ideal.Quotient.mk Q ((MulSemiringAction.toAlgHom (𝓞 F) (𝓞 E) σ)
      ((σ ^ n) • x)) = _
    rw [← H.restrict_mk, ih, pow_succ', AlgHom.mul_apply]

/-- Quotienting by actual inertia is exactly what makes Frobenius order
equal the residue degree at ramified as well as unramified primes. -/
theorem orderOf_frobenius_mod_inertia
    (P : Ideal (𝓞 F)) (Q : Ideal (𝓞 E))
    [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    (σ : E ≃ₐ[F] E) (H : IsArithFrobAt (𝓞 F) σ Q) :
    orderOf (QuotientGroup.mk σ : Gal(E/F) ⧸ Q.inertia Gal(E/F)) =
      Q.inertiaDeg (𝓞 F) := by
  have horder : orderOf (QuotientGroup.mk σ : Gal(E/F) ⧸ Q.inertia Gal(E/F)) =
      orderOf H.restrict := by
    apply orderOf_eq_orderOf_iff.mpr
    intro n
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    constructor
    · intro hn
      apply AlgHom.ext
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [← isArithFrobAt_restrict_pow_mk F E Q σ H n x]
      apply Ideal.Quotient.eq.mpr
      exact hn x
    · intro hn x
      apply Ideal.Quotient.eq.mp
      rw [isArithFrobAt_restrict_pow_mk F E Q σ H n x, hn, AlgHom.one_apply]
  let : (Q.under (𝓞 F)).IsMaximal := by
    rw [← Q.over_def P]
    infer_instance
  let : Fintype ((𝓞 F) ⧸ Q.under (𝓞 F)) := Fintype.ofFinite _
  have hr : H.restrict = FiniteField.frobeniusAlgHom
      ((𝓞 F) ⧸ Q.under (𝓞 F)) ((𝓞 E) ⧸ Q) := by
    ext x
    simp only [H.restrict_apply, FiniteField.coe_frobeniusAlgHom, Nat.card_eq_fintype_card]
  rw [horder, hr, FiniteField.orderOf_frobeniusAlgHom,
    Ideal.inertiaDeg_eq_of_isMaximal (Q.under (𝓞 F)) Q]

end ArtinMatthews.AbelianLocal
