module

public import ArtinMatthews.CubicReciprocityBridgeIntegral
public import ArtinMatthews.CubicReciprocityBridgeFrobenius
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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

/-!
# Cubic residue symbols for actual relative Frobenius lifts

This specializes the residue-field proof to the constructed integral Kummer
extension. The complex embedding agrees with the one used by the Eisenstein
characters, so no untracked conjugation remains.
-/
noncomputable section
open scoped NumberField
open OAI OAI.ActualEisensteinCubic

namespace ArtinMatthews
namespace EisensteinFrobeniusData

variable {S : Finset ℤ} {P : Ideal O} [P.IsMaximal]
    (D : EisensteinFrobeniusData S P)

/-- The selected actual relative Frobenius acts on integral cubic roots by
the genuine cubic residue symbol. -/
theorem cubic_action (hg : lambda ∉ P) {a : O} (ha : a ∉ P)
    {x : 𝓞 (integerCubicField S)}
    (hx : x ^ 3 = algebraMap O (𝓞 (integerCubicField S)) a) :
    D.frobenius • x =
      algebraMap O (𝓞 (integerCubicField S)) (cubicChar P hg (Ideal.Quotient.mk P a)) * x := by
  let : D.primeIdeal.IsMaximal := D.maximal
  let : D.primeIdeal.LiesOver P := D.liesOver
  exact arithFrob_cubic_symbol_action P D.primeIdeal hg D.frobenius D.frobenius_spec ha hx

/-- The same exact action in the ambient complex field, with the prescribed
Eisenstein orientation. -/
theorem cubic_action_complex (hg : lambda ∉ P) {a : O} (ha : a ∉ P)
    {x : 𝓞 (integerCubicField S)}
    (hx : x ^ 3 = algebraMap O (𝓞 (integerCubicField S)) a) :
    ((D.frobenius.val (x : integerCubicField S) : integerCubicField S) : ℂ) =
      ConcreteTraceCRT.eisEmbedding (cubicChar P hg (Ideal.Quotient.mk P a)) *
        ((x : integerCubicField S) : ℂ) := by
  have h := congrArg (fun y : 𝓞 (integerCubicField S) => ((y : integerCubicField S) : ℂ))
    (D.cubic_action hg ha hx)
  change ((D.frobenius.val (x : integerCubicField S) : integerCubicField S) : ℂ) =
    (((heckeKummerIntegersEmbedding S (cubicChar P hg (Ideal.Quotient.mk P a)) :
      𝓞 (integerCubicField S)) : integerCubicField S) : ℂ) *
      ((x : integerCubicField S) : ℂ) at h
  rwa [coe_heckeKummerIntegersEmbedding_complex] at h

end EisensteinFrobeniusData
end ArtinMatthews
