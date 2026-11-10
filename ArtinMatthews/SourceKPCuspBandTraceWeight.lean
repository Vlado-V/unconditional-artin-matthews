module

public import ArtinMatthews.SourceKPAdelicTraceConstantTerm
public import ArtinMatthews.SourceKPAutomorphicCompactTruncated
public import ArtinMatthews.SourceKPCuspBandTracePairing
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

/-! A weight constant along the actual unipotent fibre pulls out of its trace average. -/

namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "πY" => (fun q : SourceKPAdelicProjective K hζ =>
  sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q))

local instance sourceKPCuspBandWeightTraceMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]

theorem sourceKPCuspBandTraceWeight_eq_intertwiner
    (W : SourceKPAutomorphicCompactLevel K hζ → ℂ) {T : ℝ} (hT : 1 ≤ T) {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) (hq : 2*T ≤ sourceKPAdelicCoverHeight K hζ q)
    (hW : ∀ y : 𝔸[K], W (πY (sourceKPAdelicUpperLift K hζ y*q)) = W (πY q)) :
    (∫ y in sourceKPAdelicFundamentalDomain K,
      star (W (πY (sourceKPAdelicUpperLift K hζ y*q))) *
        sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s
          (πY (sourceKPAdelicUpperLift K hζ y*q)) ∂sourceKPAdelicTraceProduct K) =
      star (W (πY q)) * sourceKPAdelicTraceIntertwiner K hζ s q := by
  simp_rw [hW, sourceKPAutomorphicCompactTruncatedEisenstein_upper_periodization_of_high K hζ hT hs q hq]
  rw [integral_const_mul]
  congr 1
  haveI : (sourceKPAdelicTraceProduct K).IsAddHaarMeasure := by
    rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
    infer_instance
  exact sourceKPAdelicHaarUnfolding K (sourceKPAdelicTraceProduct K)
    (sourceKPAdelicIntertwiningKernel K hζ s q)
    (sourceKPAdelicIntertwiningKernel_trace_integrable K hζ hs q)

end
end ArtinMatthews
