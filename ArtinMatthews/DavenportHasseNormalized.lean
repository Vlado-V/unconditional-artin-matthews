module

public import OAI.NumberTheory.DirichletL.Detector.Gauss
public import ArtinMatthews.FiniteFieldNormCharacter
public import ArtinMatthews.DavenportHasseGauss
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

/-! The actual normalized Gauss sums have the same lifting sign, since
the positive square-root cardinalities respect extension degree. -/
namespace ArtinMatthews.DavenportHasse
open OAI.SevenEighths
noncomputable section

variable (F E : Type*) [Field F] [Field E] [Fintype F] [Fintype E] [Algebra F E]

theorem sqrt_card_extension :
    Real.sqrt (Fintype.card E : ℝ) =
      Real.sqrt (Fintype.card F : ℝ) ^ Module.finrank F E := by
  apply (Real.sqrt_eq_iff_eq_sq (Nat.cast_nonneg _)
    (pow_nonneg (Real.sqrt_nonneg _) _)).mpr
  rw [← pow_mul, Nat.mul_comm (Module.finrank F E) 2, pow_mul,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  exact_mod_cast (Module.card_eq_pow_finrank (K := F) (V := E))

theorem normalizedGauss_norm_trace (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ) :
    ProbeGauss.normalizedGauss (FiniteFieldCharacter.normLift F E χ)
      (FiniteFieldCharacter.traceLift F E ψ) =
      (-1 : ℂ)^(Module.finrank F E-1) *
        ProbeGauss.normalizedGauss χ ψ ^ Module.finrank F E := by
  unfold ProbeGauss.normalizedGauss
  rw [gaussSum_norm_trace F E χ hχ ψ,sqrt_card_extension F E,Complex.ofReal_pow,
    div_pow,mul_div_assoc]

end
end ArtinMatthews.DavenportHasse
