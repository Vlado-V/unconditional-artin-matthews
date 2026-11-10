module

public import ArtinMatthews.SourceKPAdelicIntertwinerHolomorphic
public import ArtinMatthews.SourceAdelicTraceHaar
public import ArtinMatthews.SourceKPAdelicStandardConstantTerm
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

/-! The actual constant term and holomorphic intertwining integral for
the prescribed local trace-self-dual Haar product. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPTraceConstantTermMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPTraceConstantTermBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

def sourceKPAdelicTraceIntertwiner (s : ℂ) (g : SourceKPAdelicProjective K hζ) : ℂ :=
  sourceKPAdelicIntertwiner K hζ (sourceKPAdelicTraceProduct K) s g

theorem sourceKPAdelicIntertwiningKernel_trace_integrable {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) :
    Integrable (sourceKPAdelicIntertwiningKernel K hζ s g) (sourceKPAdelicTraceProduct K) := by
  simpa only [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ] using
    sourceKPAdelicIntertwiningKernel_standard_integrable K hζ hs g

theorem sourceKPAdelicTraceIntertwiner_hasDerivAt {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) < 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) :
    HasDerivAt (fun z : ℂ => sourceKPAdelicTraceIntertwiner K hζ z g)
      (∫ y, deriv (fun z : ℂ => sourceKPAdelicIntertwiningKernel K hζ z g y) s
        ∂sourceKPAdelicTraceProduct K) s := by
  simpa only [sourceKPAdelicTraceIntertwiner,
    sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ] using
    sourceKPAdelicIntertwiner_hasDerivAt K hζ (sourceKPAdelicStandardHaar K) hs g

theorem sourceKPAdelicTraceIntertwiner_holomorphic (g : SourceKPAdelicProjective K hζ) :
    DifferentiableOn ℂ (fun s => sourceKPAdelicTraceIntertwiner K hζ s g)
      {s : ℂ | ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) < 2*s.re+1} := by
  simpa only [sourceKPAdelicTraceIntertwiner,
    sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ] using
    sourceKPAdelicIntertwiner_holomorphic K hζ (sourceKPAdelicStandardHaar K) g

theorem sourceKPAdelicCompactEisenstein_traceConstantTerm {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) :
    (∫ y in sourceKPAdelicFundamentalDomain K,
      sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y*g)
        ∂sourceKPAdelicTraceProduct K) =
      sourceKPAdelicCompactScalar K hζ s g + sourceKPAdelicTraceIntertwiner K hζ s g := by
  simpa only [sourceKPAdelicTraceIntertwiner, sourceKPAdelicIntertwiner,
    sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ] using
    sourceKPAdelicCompactEisenstein_standardConstantTerm K hζ hs g

end
end ArtinMatthews
