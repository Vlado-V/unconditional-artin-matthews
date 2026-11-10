module

public import ArtinMatthews.FullMainConditionalInputs
public import ArtinMatthews.FullMainOrdinaryActual
public import ArtinMatthews.FullMainPhysicalInputs
public import ArtinMatthews.SourceReflectionLiteralActual
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The fixed ordinary cancellation and actual angular expansion prove
the original simultaneous primitive-root theorem. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField

theorem giantAngularSourceInput_actual : GiantAngularSourceInput := by
  intro q _ _ _
  let K := twelfthCyclotomicField q
  let hz := twelfthAngularRoot_isPrimitiveRoot q
  apply twelfthAngularSourceBounds_of_literal_expansions q
  · exact sourceReflectionLiteralExpansion_actual K hz (angularReflectedSeed K ⊤)
      (angularReflectedSeed_bad_subset K ⊤) (principalAngularTrivialRay K)
      top_ne_bot (angularReflectedSeed_cutoff_subset K ⊤)
  · intro J hJ ψ _ _ _ _
    exact sourceReflectionLiteralExpansion_actual K hz (angularReflectedSeed K J)
      (angularReflectedSeed_bad_subset K J) ψ hJ (angularReflectedSeed_cutoff_subset K J)

theorem main_result : FullMainStatement :=
  fullMainStatement_of_angular_input giantAngularSourceInput_actual

end ArtinMatthews
