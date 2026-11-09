module

public import ArtinMatthews.EisensteinAngularNorm
public import ArtinMatthews.EisensteinAngularResidue
public import ArtinMatthews.VaryingKummerAnalyticIdealTraceCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! The global norm-pullback angular character agrees with the cubic
Gauss phase at an actual prime of an extension of the Eisenstein field.
The residue character has the literal power-residue reduction, and the
statement holds for every primitive additive phase. -/
namespace ArtinMatthews.AngularLambda
open OAI OAI.ActualEisensteinCubic OAI.ConcreteTraceCRT OAI.SevenEighths
open NumberField
open scoped NumberField Classical
noncomputable section

variable (F : Type*) [Field F] [NumberField F] [Algebra BaseField F]
variable (P : Ideal (𝓞 F)) [P.IsMaximal]
variable (q : Ideal BaseIntegers) [q.IsMaximal] [P.LiesOver q]
variable (hq : lambda ∉ q)
local instance : Field (BaseIntegers ⧸ q) := Ideal.Quotient.field q
local instance : Field ((𝓞 F) ⧸ P) := Ideal.Quotient.field P
local instance : Fintype (BaseIntegers ⧸ q) := Fintype.ofFinite _
local instance : Fintype ((𝓞 F) ⧸ P) := Fintype.ofFinite _

def angularPrimeSexticCharacter : MulChar ((𝓞 F) ⧸ P) ℂ :=
  complexSexticResidueNormLift q hq ((𝓞 F) ⧸ P)

theorem angularNormIdeal_prime : angularNormIdeal F P =
    eisensteinAngularIdeal q ^ Module.finrank (BaseIntegers ⧸ q) ((𝓞 F) ⧸ P) := by
  rw [angularNormIdeal_apply,Ideal.relNorm_eq_pow_of_isMaximal P q,map_pow,
    Ideal.inertiaDeg_eq_of_isMaximal q P]

theorem angularPrimeCubicCharacter_power_residue (x : (𝓞 F) ⧸ P) :
    Ideal.Quotient.mk P (algebraMap BaseIntegers (𝓞 F)
      (cubicResidueNormLift q hq ((𝓞 F) ⧸ P) x)) =
      x ^ ((Nat.card ((𝓞 F) ⧸ P)-1)/3) := by
  rw [← Ideal.Quotient.algebraMap_mk_of_liesOver P q]
  exact cubicResidueNormLift_reduce q hq ((𝓞 F) ⧸ P) x

theorem angularPrime_gammaTwo_cube (ψ : AddChar ((𝓞 F) ⧸ P) ℂ) (hψ : ψ.IsPrimitive) :
    VaryingKummerAnalytic.probeGaussGamma (angularPrimeSexticCharacter F P q hq) ψ 2 ^ 3 =
      -angularNormIdeal F P := by
  rw [angularPrimeSexticCharacter,sexticNormLift_gammaTwo_cube,angularNormIdeal_prime F P q]
  exact hψ

def angularPrimeTracePhase (hP : P ≠ ⊥) : AddChar ((𝓞 F) ⧸ P) ℂ :=
  (VaryingKummerAnalytic.idealTraceAddChar F P hP)⁻¹

omit [Algebra BaseField F] [P.IsMaximal] in
theorem angularPrimeTracePhase_isPrimitive (hP : P ≠ ⊥) :
    (angularPrimeTracePhase F P hP).IsPrimitive := by
  intro x hx
  rw [angularPrimeTracePhase,AddChar.inv_mulShift,AddChar.mulShift_mulShift,neg_one_mul]
  exact VaryingKummerAnalytic.idealTraceAddChar_isPrimitive F P hP (neg_ne_zero.mpr hx)

theorem angularPrime_trace_gammaTwo_cube (hP : P ≠ ⊥) :
    VaryingKummerAnalytic.probeGaussGamma (angularPrimeSexticCharacter F P q hq)
      (angularPrimeTracePhase F P hP) 2 ^ 3 = -angularNormIdeal F P :=
  angularPrime_gammaTwo_cube F P q hq _ (angularPrimeTracePhase_isPrimitive F P hP)

end
end ArtinMatthews.AngularLambda
