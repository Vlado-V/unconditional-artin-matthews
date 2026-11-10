module

public import ArtinMatthews.KummerAngularOfReflected
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain StandardAdelic QuadraticWeil
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]

/-- The actual source Weil condition contains every trace-bad place. -/
theorem sourceTraceBadPlaces_subset_of_weil
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀) :
    traceBadPlaces F ⊆ sourceHilbertSet F S₀ :=
  fun _ hp => hBad (Finset.mem_union_left _ hp)

/-- Every finite set used by the twelfth-cyclotomic angular source includes the trace-bad places. -/
theorem angularReflectedSeed_trace_subset (J : Ideal (𝓞 F)) :
    traceBadPlaces F ⊆
      sourceHilbertSet F (VaryingKummerAnalytic.angularReflectedSeed F J) :=
  sourceTraceBadPlaces_subset_of_weil F _
    (VaryingKummerAnalytic.angularReflectedSeed_bad_subset F J)

end
end ArtinMatthews.SourceEulerAssembly
