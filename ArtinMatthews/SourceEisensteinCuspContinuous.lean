module

public import ArtinMatthews.SourceEisensteinCuspMean
public import ArtinMatthews.SourceKPCuspSobolev
public import ArtinMatthews.SourceEisensteinUpperContinuity
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

/-! The actual cusp remainder is a continuous zero-mean function, hence an
actual trace-Haar L2 vector on the genuine principal cusp torus. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (g : SourceKPAdelicProjective K hζ)
local notation "D" => sourceKPCuspChosenPeriod K hζ g
local notation "Q" => SourceKPCuspPrincipalQuotient K D
local instance sourceEisensteinCuspContinuousMeasurable : MeasurableSpace Q := borel Q
local instance sourceEisensteinCuspContinuousBorel : BorelSpace Q := ⟨rfl⟩

theorem sourceKPCuspNonconstantEisenstein_continuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1) :
    Continuous (sourceKPCuspNonconstantEisenstein K hζ g s) := by
  apply (QuotientAddGroup.isQuotientMap_mk (sourceKPCuspPrincipalPeriods K D)).continuous_iff.mpr
  simpa only [Function.comp_def, sourceKPCuspNonconstantEisenstein_mk] using
    sourceKPAdelicNonconstantEisenstein_upper_continuous K hζ hs g

def sourceKPCuspNonconstantEisensteinContinuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1) : C(Q,ℂ) :=
  ⟨sourceKPCuspNonconstantEisenstein K hζ g s,
    sourceKPCuspNonconstantEisenstein_continuous K hζ g hs⟩

theorem sourceKPCuspNonconstantEisenstein_actual_mean_zero {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1) :
    (∫ q, sourceKPCuspNonconstantEisenstein K hζ g s q ∂sourceKPCuspTraceHaar K D) = 0 :=
  sourceKPCuspNonconstantEisenstein_mean_zero K hζ g hs
    (sourceKPCuspNonconstantEisenstein_continuous K hζ g hs).aestronglyMeasurable

def sourceKPCuspNonconstantEisensteinL2 {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1) : SourceKPCuspL2 K D :=
  sourceKPCuspContinuousL2 K D hζ (sourceKPCuspChosenPeriod_ne_zero K hζ g)
    (sourceKPCuspNonconstantEisensteinContinuous K hζ g hs)

theorem sourceKPCuspNonconstantEisensteinL2_coe {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1) :
    sourceKPCuspNonconstantEisensteinL2 K hζ g hs =ᵐ[sourceKPCuspTraceHaar K D]
      sourceKPCuspNonconstantEisenstein K hζ g s :=
  sourceKPCuspContinuousL2_coe K D hζ (sourceKPCuspChosenPeriod_ne_zero K hζ g)
    (sourceKPCuspNonconstantEisensteinContinuous K hζ g hs)

theorem sourceKPCuspNonconstantEisensteinL2_mean_zero {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1) :
    (∫ q, sourceKPCuspNonconstantEisensteinL2 K hζ g hs q ∂sourceKPCuspTraceHaar K D) = 0 :=
  (integral_congr_ae (sourceKPCuspNonconstantEisensteinL2_coe K hζ g hs)).trans
    (sourceKPCuspNonconstantEisenstein_actual_mean_zero K hζ g hs)

end
end ArtinMatthews
