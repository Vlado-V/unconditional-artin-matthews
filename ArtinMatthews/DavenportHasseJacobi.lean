module

public import Mathlib.NumberTheory.JacobiSum.Basic
public import ArtinMatthews.FiniteFieldNormCharacter
public import ArtinMatthews.DavenportHasseGauss
public import Mathlib.NumberTheory.LegendreSymbol.Complex
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Exact Jacobi-sum norm lifting, obtained by dividing the three
proved Gauss lifting identities. -/
namespace ArtinMatthews.DavenportHasse
open scoped Classical
noncomputable section

variable (F E : Type*) [Field F] [Field E] [Fintype F] [Fintype E] [Algebra F E]

theorem jacobiSum_norm_lift_of_primitive (χ θ : MulChar F ℂ)
    (hχ : χ ≠ 1) (hθ : θ ≠ 1) (hχθ : χ*θ ≠ 1)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    jacobiSum (FiniteFieldCharacter.normLift F E χ) (FiniteFieldCharacter.normLift F E θ) =
      (-1 : ℂ)^(Module.finrank F E-1) * (jacobiSum χ θ)^(Module.finrank F E) := by
  have hψne : ψ ≠ 1 := by
    simpa only [AddChar.mulShift_one] using hψ (a := 1) one_ne_zero
  have hmul : FiniteFieldCharacter.normLift F E (χ*θ) =
      FiniteFieldCharacter.normLift F E χ * FiniteFieldCharacter.normLift F E θ :=
    (FiniteFieldCharacter.normLiftHom F E).map_mul χ θ
  have hlift : FiniteFieldCharacter.normLift F E χ *
      FiniteFieldCharacter.normLift F E θ ≠ 1 := by
    rw [← hmul]
    exact (FiniteFieldCharacter.normLift_ne_one_iff F E _).mpr hχθ
  have hcardF : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  have hcardE : (Fintype.card E : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  rw [jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum hcardE hlift
      (FiniteFieldCharacter.traceLift_primitive F E ψ hψne),
    ← hmul,
    gaussSum_norm_trace F E χ hχ ψ,gaussSum_norm_trace F E θ hθ ψ,
    gaussSum_norm_trace F E (χ*θ) hχθ ψ,
    jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum hcardF hχθ hψ,
    div_pow,mul_pow]
  have hs : (-1 : ℂ)^(Module.finrank F E-1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hg : (gaussSum (χ*θ) ψ)^(Module.finrank F E) ≠ 0 :=
    pow_ne_zero _ (gaussSum_ne_zero_of_nontrivial hcardF hχθ hψ)
  field_simp

/-- The Jacobi lift depends only on the norm-lifted multiplicative
characters; the auxiliary primitive additive character is constructed. -/
theorem jacobiSum_norm_lift (χ θ : MulChar F ℂ)
    (hχ : χ ≠ 1) (hθ : θ ≠ 1) (hχθ : χ*θ ≠ 1) :
    jacobiSum (FiniteFieldCharacter.normLift F E χ) (FiniteFieldCharacter.normLift F E θ) =
      (-1 : ℂ)^(Module.finrank F E-1) * (jacobiSum χ θ)^(Module.finrank F E) :=
  jacobiSum_norm_lift_of_primitive F E χ θ hχ hθ hχθ
    (AddChar.FiniteField.primitiveChar_to_Complex F)
    (AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F)

end
end ArtinMatthews.DavenportHasse
