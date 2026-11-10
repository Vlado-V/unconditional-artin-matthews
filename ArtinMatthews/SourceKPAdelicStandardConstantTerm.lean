module

public import ArtinMatthews.SourceAdelicStandardHaar
public import ArtinMatthews.SourceKPAdelicConstantTermPeriodization
public import ArtinMatthews.SourceKPAdelicKernelContinuity
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

/-! The actual constant term with the explicit adelic Haar measure
whose rational fundamental domain has mass one. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPStandardConstantTermMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPStandardConstantTermBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

theorem sourceKPAdelicIntertwiningKernel_standard_integrable {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) :
    Integrable (sourceKPAdelicIntertwiningKernel K hζ s g) (sourceKPAdelicStandardHaar K) :=
  sourceKPAdelicIntertwiningKernel_integrable K hζ (sourceKPAdelicStandardHaar K) hs g

theorem sourceKPAdelicCompactEisenstein_standardConstantTerm {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) :
    (∫ y in sourceKPAdelicFundamentalDomain K,
      sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y*g)
        ∂sourceKPAdelicStandardHaar K) =
      sourceKPAdelicCompactScalar K hζ s g +
        ∫ y, sourceKPAdelicIntertwiningKernel K hζ s g y ∂sourceKPAdelicStandardHaar K := by
  have h := sourceKPAdelicCompactEisenstein_constantTerm K hζ (sourceKPAdelicStandardHaar K) hs g
  simpa only [Measure.real, sourceKPAdelicStandardHaar_fundamentalDomain,
    ENNReal.toReal_one, one_smul] using h

end
end ArtinMatthews
