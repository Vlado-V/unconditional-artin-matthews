module

public import ArtinMatthews.SourceEisensteinNonconstant
public import ArtinMatthews.SourceKPAutomorphicEisenstein
public import ArtinMatthews.SourceKPCuspLevelPoincare
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
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

/-! The actual nonconstant term on the principal cusp torus. Its mean is the
proved adelic constant term through the genuine trace-Haar pushforward. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (g : SourceKPAdelicProjective K hζ)
local notation "D" => sourceKPCuspChosenPeriod K hζ g
local notation "Q" => SourceKPCuspPrincipalQuotient K D
local instance sourceEisensteinCuspMeanAdelicMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceEisensteinCuspMeanAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance sourceEisensteinCuspMeanQuotientMeasurable : MeasurableSpace Q := borel Q
local instance sourceEisensteinCuspMeanQuotientBorel : BorelSpace Q := ⟨rfl⟩

def sourceKPCuspNonconstantEisenstein (s : ℂ) (q : Q) : ℂ :=
  sourceKPAutomorphicEisenstein K hζ s (sourceKPCuspChosenCover K hζ g q) -
    (sourceKPAdelicCompactScalar K hζ s g + sourceKPAdelicTraceIntertwiner K hζ s g)

theorem sourceKPCuspNonconstantEisenstein_mk (s : ℂ) (a : 𝔸[K]) :
    sourceKPCuspNonconstantEisenstein K hζ g s (QuotientAddGroup.mk a) =
      sourceKPAdelicNonconstantEisenstein K hζ s (sourceKPAdelicUpperLift K hζ a * g) := by
  change sourceKPAutomorphicEisenstein K hζ s
      (sourceKPAutomorphicLevelMk K hζ (sourceKPAdelicUpperLift K hζ a * g)) - _ = _
  rw [sourceKPAutomorphicEisenstein_mk, sourceKPAdelicNonconstantEisenstein_upper]

theorem sourceKPCuspNonconstantEisenstein_integrable {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (hmeas : AEStronglyMeasurable (sourceKPCuspNonconstantEisenstein K hζ g s)
      (sourceKPCuspTraceHaar K D)) :
    Integrable (sourceKPCuspNonconstantEisenstein K hζ g s) (sourceKPCuspTraceHaar K D) := by
  change AEStronglyMeasurable (sourceKPCuspNonconstantEisenstein K hζ g s)
    (Measure.map (QuotientAddGroup.mk : 𝔸[K] → Q)
      ((sourceKPAdelicTraceProduct K).restrict (sourceKPAdelicFundamentalDomain K))) at hmeas
  apply (integrable_map_measure hmeas QuotientAddGroup.continuous_mk.measurable.aemeasurable).mpr
  simpa only [Function.comp_def, sourceKPCuspNonconstantEisenstein_mk, IntegrableOn] using
    sourceKPAdelicNonconstantEisenstein_trace_integrable K hζ hs g

theorem sourceKPCuspNonconstantEisenstein_mean_zero {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (hmeas : AEStronglyMeasurable (sourceKPCuspNonconstantEisenstein K hζ g s)
      (sourceKPCuspTraceHaar K D)) :
    (∫ q, sourceKPCuspNonconstantEisenstein K hζ g s q ∂sourceKPCuspTraceHaar K D) = 0 := by
  rw [sourceKPCuspTraceHaar, integral_map QuotientAddGroup.continuous_mk.measurable.aemeasurable hmeas]
  simpa only [sourceKPCuspNonconstantEisenstein_mk] using
    sourceKPAdelicNonconstantEisenstein_trace_mean_zero K hζ hs g

end
end ArtinMatthews
