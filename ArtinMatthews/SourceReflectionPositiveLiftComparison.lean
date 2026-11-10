module

public import ArtinMatthews.SourceReflectionPositiveTameFourier
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! At a nonzero Fourier label the positive upper translation is the
same upper argument as in the actual tame Weyl rotation. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField Classical

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "R" => (𝓞 K) ⧸ P.val.asIdeal
local notation "L" => P.val.adicCompletion K

attribute [local instance] positiveResidueField

theorem sourceReflectionPositiveLocalTranslation_unit (a : Rˣ) :
    sourceReflectionPositiveLocalTranslation K hζ S₀ P (a : R) =
      ((sourceKPTameExteriorUniformizer K hζ S₀ P ^ (-1 : ℤ) *
        sourceReflectionTameUnitLift K S₀ P a : Lˣ) : L) := by
  rw [sourceReflectionPositiveLocalTranslation, sourceReflectionPositiveResidueLift,
    dite_eq_right (Units.ne_zero a), Units.val_mul, Units.val_zpow_eq_zpow_val, zpow_neg_one]
  change (_ : L) * (sourceReflectionTameUnitLift K S₀ P (Units.mk0 (a:R) a.ne_zero) : L) =
    _ * (sourceReflectionTameUnitLift K S₀ P a : L)
  rw [show Units.mk0 (a:R) a.ne_zero = a from Units.ext rfl]

end
end ArtinMatthews
