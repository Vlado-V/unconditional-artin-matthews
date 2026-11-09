module

public import ArtinMatthews.EisensteinAngularJacobi
public import ArtinMatthews.CubicGaussJacobi
public import ArtinMatthews.FiniteFieldPowerResidueNorm
public import OAI.NumberTheory.DirichletL.GaussSum.CubicNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! The actual residue-field norm lift has the power-residue values and
the cubic angular Gauss value. Every primitive additive phase gives the
same cube. -/
namespace ArtinMatthews.AngularLambda
open OAI OAI.ActualEisensteinCubic OAI.CompletedGauss OAI.ConcreteTraceCRT
open OAI.SevenEighths
open scoped Classical
noncomputable section

variable (q : Ideal BaseIntegers) [q.IsMaximal] (hq : lambda ∉ q)
local instance : Field (BaseIntegers ⧸ q) := Ideal.Quotient.field q
local instance : Fintype (BaseIntegers ⧸ q) := Fintype.ofFinite _
variable (E : Type*) [Field E] [Fintype E] [Algebra (BaseIntegers ⧸ q) E]

def cubicResidueNormLift : MulChar E BaseIntegers :=
  FiniteFieldCharacter.normLift (BaseIntegers ⧸ q) E (cubicChar q hq)

theorem cubicResidueNormLift_reduce (x : E) :
    algebraMap (BaseIntegers ⧸ q) E
      (Ideal.Quotient.mk q (cubicResidueNormLift q hq E x)) =
      x^((Nat.card E-1)/3) := by
  rw [cubicResidueNormLift,FiniteFieldCharacter.normLift_apply,cubicChar_reduce]
  exact FiniteFieldCharacter.norm_power_residue (BaseIntegers ⧸ q) E 3
    (card_sub_one_div_three q hq) x

theorem cubicResidueNormLift_complex :
    (cubicResidueNormLift q hq E).ringHomComp eisEmbedding =
      FiniteFieldCharacter.normLift (BaseIntegers ⧸ q) E (eisensteinCubicCharacter q hq) := by
  ext x
  rfl

theorem eisensteinCubicNormLift_normalized_cube (ψ : AddChar E ℂ) (hψ : ψ.IsPrimitive) :
    ProbeGauss.normalizedGauss
      (FiniteFieldCharacter.normLift (BaseIntegers ⧸ q) E (eisensteinCubicCharacter q hq)) ψ ^ 3 =
      -(eisensteinAngularIdeal q ^ Module.finrank (BaseIntegers ⧸ q) E) := by
  have hord : orderOf
      (FiniteFieldCharacter.normLift (BaseIntegers ⧸ q) E (eisensteinCubicCharacter q hq)) = 3 := by
    rw [FiniteFieldCharacter.normLift_orderOf,eisensteinCubicCharacter_order]
  have hnorm : (Real.sqrt (Fintype.card (BaseIntegers ⧸ q) : ℝ) : ℂ) =
      (‖eisEmbedding (primaryGenerator q)‖ : ℂ) := by
    have hn := primaryGenerator_norm q (primaryGenerator_prime_ne_zero q hq)
    have hc : Ideal.absNorm q = Fintype.card (BaseIntegers ⧸ q) := by
      rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
    rw [hc] at hn
    exact congrArg (fun x : ℝ => (x : ℂ)) hn.symm
  rw [normalizedCubicGauss_cube_eq_jacobi _ hord ψ hψ,
    eisensteinCubicCharacter_lifted_jacobi,
    DavenportHasse.sqrt_card_extension (BaseIntegers ⧸ q) E,Complex.ofReal_pow,hnorm,
    eisensteinAngularIdeal_apply,complexAngular,div_pow,neg_div]

def sexticResidueNormLift : MulChar E BaseIntegers :=
  FiniteFieldCharacter.normLift (BaseIntegers ⧸ q) E (sexticChar q hq)

def complexSexticResidueNormLift : MulChar E ℂ :=
  (sexticResidueNormLift q hq E).ringHomComp eisEmbedding

theorem complexSexticResidueNormLift_order (hchar : ringChar (BaseIntegers ⧸ q) ≠ 2) :
    orderOf (complexSexticResidueNormLift q hq E) = 6 := by
  have h := orderOf_injective (MulChar.ringHomCompHom (R := E) eisEmbedding)
    (MulChar.injective_ringHomComp eisEmbedding_injective) (sexticResidueNormLift q hq E)
  have h' : orderOf ((sexticResidueNormLift q hq E).ringHomComp eisEmbedding) =
      orderOf (sexticResidueNormLift q hq E) := h
  rw [complexSexticResidueNormLift,h',sexticResidueNormLift,
    FiniteFieldCharacter.normLift_orderOf,sexticChar_order q hq hchar]

theorem sexticResidueNormLift_reduce_unit (hchar : ringChar (BaseIntegers ⧸ q) ≠ 2)
    (u : Eˣ) :
    algebraMap (BaseIntegers ⧸ q) E
      (Ideal.Quotient.mk q (sexticResidueNormLift q hq E (u : E))) =
      (u : E)^((Nat.card E-1)/6) := by
  have hred : Ideal.Quotient.mk q
      (sexticChar q hq (Algebra.norm (BaseIntegers ⧸ q) (u : E))) =
      (Algebra.norm (BaseIntegers ⧸ q) (u : E))^((Nat.card (BaseIntegers ⧸ q)-1)/6) :=
    sexticChar_reduce_unit q hq hchar (Units.map (Algebra.norm (BaseIntegers ⧸ q)) u)
  have hdiv : 6 ∣ Nat.card (BaseIntegers ⧸ q)-1 := by
    have h3 : 3 ∣ Fintype.card (BaseIntegers ⧸ q)-1 := by
      simpa only [Nat.card_eq_fintype_card] using card_sub_one_div_three q hq
    have hodd : Fintype.card (BaseIntegers ⧸ q) % 2 = 1 :=
      FiniteField.odd_card_of_char_ne_two hchar
    rw [Nat.card_eq_fintype_card]
    omega
  rw [sexticResidueNormLift,FiniteFieldCharacter.normLift_apply,hred]
  exact FiniteFieldCharacter.norm_power_residue (BaseIntegers ⧸ q) E 6 hdiv (u : E)

theorem complexSexticResidueNormLift_sq :
    complexSexticResidueNormLift q hq E ^ 2 =
      FiniteFieldCharacter.normLift (BaseIntegers ⧸ q) E (eisensteinCubicCharacter q hq) := by
  rw [complexSexticResidueNormLift,MulChar.ringHomComp_pow,sexticResidueNormLift,
    ← FiniteFieldCharacter.normLift_pow,(sexticChar_powers q hq).1]
  exact cubicResidueNormLift_complex q hq E

theorem sexticNormLift_gammaTwo_cube (ψ : AddChar E ℂ) (hψ : ψ.IsPrimitive) :
    VaryingKummerAnalytic.probeGaussGamma (complexSexticResidueNormLift q hq E) ψ 2 ^ 3 =
      -(eisensteinAngularIdeal q ^ Module.finrank (BaseIntegers ⧸ q) E) := by
  rw [VaryingKummerAnalytic.probeGaussGamma,complexSexticResidueNormLift_sq]
  exact eisensteinCubicNormLift_normalized_cube q hq E ψ hψ

end
end ArtinMatthews.AngularLambda
