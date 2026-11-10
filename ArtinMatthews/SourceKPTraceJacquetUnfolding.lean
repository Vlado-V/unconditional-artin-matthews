module

public import ArtinMatthews.SourceAdelicHaarUnfolding
public import ArtinMatthews.SourceAdelicTraceHaar
public import ArtinMatthews.SourceKPAdelicConstantTermPeriodization
public import ArtinMatthews.SourceKPTraceJacquetCharacter
public import ArtinMatthews.SourceKPAdelicTraceConstantTerm
public import ArtinMatthews.SourceKPTraceJacquetMean
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

/-! The actual nonzero-frequency coefficient of the Eisenstein
series unfolds on the same trace Haar measure as the constant term.
The incoming term disappears by the proved trace-character mean. -/

namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPTraceJacquetUnfoldingMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPTraceJacquetUnfoldingBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

def sourceKPAdelicTraceJacquetKernel (m : Kˣ) (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) : ℂ :=
  sourceKPTraceJacquetCharacter K m y * sourceKPAdelicIntertwiningKernel K hζ s g y

theorem sourceKPAdelicTraceJacquetKernel_norm (m : Kˣ) (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) :
    ‖sourceKPAdelicTraceJacquetKernel K hζ m s g y‖ =
      ‖sourceKPAdelicIntertwiningKernel K hζ s g y‖ := by
  rw [sourceKPAdelicTraceJacquetKernel, norm_mul, sourceKPTraceJacquetCharacter_norm, one_mul]

theorem sourceKPAdelicTraceJacquetKernel_integrable {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (m : Kˣ) (g : SourceKPAdelicProjective K hζ) :
    Integrable (sourceKPAdelicTraceJacquetKernel K hζ m s g) (sourceKPAdelicTraceProduct K) := by
  exact (sourceKPAdelicIntertwiningKernel_trace_integrable K hζ hs g).bdd_mul
    (sourceKPTraceJacquetCharacter_continuous K m).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => (sourceKPTraceJacquetCharacter_norm K m y).le)

theorem sourceKPTraceJacquetCharacter_periodization (m : Kˣ) (f : 𝔸[K] → ℂ) (y : 𝔸[K]) :
    sourceKPAdelicPeriodization K (fun x => sourceKPTraceJacquetCharacter K m x * f x) y =
      sourceKPTraceJacquetCharacter K m y * sourceKPAdelicPeriodization K f y := by
  unfold sourceKPAdelicPeriodization
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  exact congrArg (fun c => c * f (y+algebraMap K 𝔸[K] q))
    (sourceKPTraceJacquetCharacter_rational_add K m q y)

theorem sourceKPAdelicCompactEisenstein_traceJacquet_periodization {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (m : Kˣ) (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) :
    sourceKPTraceJacquetCharacter K m y *
      sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y*g) =
    sourceKPTraceJacquetCharacter K m y * sourceKPAdelicCompactScalar K hζ s g +
      sourceKPAdelicPeriodization K (sourceKPAdelicTraceJacquetKernel K hζ m s g) y := by
  let f := sourceKPAdelicIntertwiningKernel K hζ s g
  have he : sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y*g) =
      sourceKPAdelicCompactScalar K hζ s g + sourceKPAdelicPeriodization K f y := by
    rw [sourceKPAdelicCompactEisenstein_upper_periodization K hζ hs g y, sourceKPAdelicPeriodization]
    congr 1
    apply tsum_congr
    intro q
    exact congrArg f (add_comm _ _)
  rw [he, mul_add]
  change _ = _ + sourceKPAdelicPeriodization K (fun t => sourceKPTraceJacquetCharacter K m t * f t) y
  rw [sourceKPTraceJacquetCharacter_periodization]

theorem sourceKPAdelicCompactEisenstein_traceJacquet {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (m : Kˣ) (g : SourceKPAdelicProjective K hζ) :
    (∫ y in sourceKPAdelicFundamentalDomain K,
      sourceKPTraceJacquetCharacter K m y *
        sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y*g)
      ∂sourceKPAdelicTraceProduct K) =
    ∫ y, sourceKPAdelicTraceJacquetKernel K hζ m s g y ∂sourceKPAdelicTraceProduct K := by
  let μ := sourceKPAdelicTraceProduct K
  let D := sourceKPAdelicFundamentalDomain K
  letI : μ.IsAddHaarMeasure := by
    change (sourceKPAdelicTraceProduct K).IsAddHaarMeasure
    rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
    infer_instance
  let F := sourceKPAdelicTraceJacquetKernel K hζ m s g
  have hF : Integrable F μ := sourceKPAdelicTraceJacquetKernel_integrable K hζ hs m g
  have hC : IntegrableOn (fun y => sourceKPTraceJacquetCharacter K m y *
      sourceKPAdelicCompactScalar K hζ s g) D μ :=
    (sourceKPTraceJacquetCharacter_integrableOn K hζ m).mul_const _
  have hP : IntegrableOn (sourceKPAdelicPeriodization K F) D μ :=
    sourceKPAdelicPeriodization_integrable K μ F hF
  calc
    _ = ∫ y in D, (sourceKPTraceJacquetCharacter K m y * sourceKPAdelicCompactScalar K hζ s g +
        sourceKPAdelicPeriodization K F y) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall
        (sourceKPAdelicCompactEisenstein_traceJacquet_periodization K hζ hs m g))
    _ = (∫ y in D, sourceKPTraceJacquetCharacter K m y * sourceKPAdelicCompactScalar K hζ s g ∂μ) +
        ∫ y in D, sourceKPAdelicPeriodization K F y ∂μ := integral_add hC hP
    _ = _ := by
      rw [integral_mul_const, sourceKPTraceJacquetCharacter_integral_zero K hζ m, zero_mul, zero_add,
        sourceKPAdelicHaarUnfolding K μ F hF]

end
end ArtinMatthews
