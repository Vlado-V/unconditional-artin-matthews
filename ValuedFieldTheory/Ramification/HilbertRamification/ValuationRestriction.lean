module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions
public import ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups
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

set_option autoImplicit false

/-!
# Compatibility of valuation-ring actions with Galois restriction

For a normal field tower `M / L / K` with uniquely extended discrete
valuations, the valuation-ring action of an automorphism of `M / K` on an
element coming from `L` is the image of the valuation-ring action of its
restriction to `L / K`.
-/

noncomputable section

universe u v w x y z

namespace RamificationTheory.HilbertRamification
namespace Higher

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {L : Type w} {M : Type y}
variable [Field K] [Field L] [Field M]
variable [Algebra K L] [Algebra K M] [Algebra L M]
variable [IsScalarTower K L M] [Normal K L]
variable {base : DVF.{u, v} K}
variable {middle : DVF.{w, x} L}
variable {target : DVF.{y, z} M}
variable [base.valuation.HasExtension middle.valuation]
variable [middle.valuation.HasExtension target.valuation]
variable [base.valuation.HasExtension target.valuation]

/-- Acting on an integral element from a normal intermediate field and then
viewing it in the top valuation ring agrees with first restricting the
Galois automorphism and acting in the intermediate valuation ring. -/
theorem
    valuationSubringAutOfUniqueExtension_integerMap_restrictNormal
    (hmiddle :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base middle)
    (htarget :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base target)
    (σ : Gal(M / K)) (a : middle.valuationSubring) :
    valuationSubringAutOfUniqueExtension
          (base := base) (target := target) htarget σ
          (integerMap middle target a) =
      integerMap middle target
        (valuationSubringAutOfUniqueExtension
          (base := base) (target := middle) hmiddle
          (σ.restrictNormal L) a) := by
  apply Subtype.ext
  change
    σ (algebraMap L M (a : L)) =
      algebraMap L M ((σ.restrictNormal L) (a : L))
  exact (AlgEquiv.restrictNormal_commutes σ L (a : L)).symm

end Higher
end RamificationTheory.HilbertRamification

end
