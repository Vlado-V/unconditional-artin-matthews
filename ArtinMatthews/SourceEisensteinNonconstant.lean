module

public import ArtinMatthews.SourceKPAdelicTraceConstantTerm
public import ArtinMatthews.SourceAdelicHaarUnfolding
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

/-! The genuine nonconstant Eisenstein remainder has zero adelic unipotent mean. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory Filter
open scoped NumberField AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceCuspNonconstantAdelicMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceCuspNonconstantAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

theorem sourceKPAdelicIntertwiningKernel_upper (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (x y : 𝔸[K]) :
    sourceKPAdelicIntertwiningKernel K hζ s (sourceKPAdelicUpperLift K hζ y * g) x =
      sourceKPAdelicIntertwiningKernel K hζ s g (x + y) := by
  unfold sourceKPAdelicIntertwiningKernel
  rw [sourceKPAdelicUpperLift_add]
  simp only [mul_assoc]

theorem sourceKPAdelicIntertwiner_upper (μ : Measure 𝔸[K]) [μ.IsAddHaarMeasure]
    (s : ℂ) (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) :
    sourceKPAdelicIntertwiner K hζ μ s (sourceKPAdelicUpperLift K hζ y * g) =
      sourceKPAdelicIntertwiner K hζ μ s g := by
  unfold sourceKPAdelicIntertwiner
  simp_rw [sourceKPAdelicIntertwiningKernel_upper]
  exact integral_add_right_eq_self _ y

theorem sourceKPAdelicTraceIntertwiner_upper (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) :
    sourceKPAdelicTraceIntertwiner K hζ s (sourceKPAdelicUpperLift K hζ y * g) =
      sourceKPAdelicTraceIntertwiner K hζ s g := by
  unfold sourceKPAdelicTraceIntertwiner
  rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
  exact sourceKPAdelicIntertwiner_upper K hζ _ s g y

def sourceKPAdelicNonconstantEisenstein (s : ℂ) (g : SourceKPAdelicProjective K hζ) : ℂ :=
  sourceKPAdelicCompactEisenstein K hζ s g -
    (sourceKPAdelicCompactScalar K hζ s g + sourceKPAdelicTraceIntertwiner K hζ s g)

theorem sourceKPAdelicNonconstantEisenstein_upper (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) :
    sourceKPAdelicNonconstantEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y * g) =
      sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y * g) -
        (sourceKPAdelicCompactScalar K hζ s g + sourceKPAdelicTraceIntertwiner K hζ s g) := by
  unfold sourceKPAdelicNonconstantEisenstein
  rw [sourceKPAdelicTraceIntertwiner_upper]
  congr 2
  exact sourceKPAdelicPrincipalSeriesScalar_upper K hζ s (sourceKPAdelicCompactSection K hζ s) y g

theorem sourceKPAdelicCompactEisenstein_trace_integrable {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (g : SourceKPAdelicProjective K hζ) :
    IntegrableOn (fun y => sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y * g))
      (sourceKPAdelicFundamentalDomain K) (sourceKPAdelicTraceProduct K) := by
  rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
  let μ := sourceKPAdelicStandardHaar K
  let F := sourceKPAdelicIntertwiningKernel K hζ s g
  have hF : Integrable F μ := sourceKPAdelicIntertwiningKernel_standard_integrable K hζ hs g
  have hP := sourceKPAdelicPeriodization_integrable K μ F hF
  have hC : IntegrableOn (fun _ : 𝔸[K] => sourceKPAdelicCompactScalar K hζ s g)
      (sourceKPAdelicFundamentalDomain K) μ :=
    integrableOn_const (sourceKPAdelicFundamentalDomain_measure_lt_top K μ).ne
  apply (hC.add hP).congr
  filter_upwards with y
  rw [sourceKPAdelicCompactEisenstein_upper_periodization K hζ hs g y]
  simp only [Pi.add_apply]
  congr 1
  unfold sourceKPAdelicPeriodization
  apply tsum_congr
  intro x
  exact congrArg F (add_comm _ _)

theorem sourceKPAdelicNonconstantEisenstein_trace_integrable {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (g : SourceKPAdelicProjective K hζ) :
    IntegrableOn (fun y => sourceKPAdelicNonconstantEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y * g))
      (sourceKPAdelicFundamentalDomain K) (sourceKPAdelicTraceProduct K) := by
  have hm : sourceKPAdelicTraceProduct K (sourceKPAdelicFundamentalDomain K) ≠ ⊤ := by
    rw [sourceKPAdelicTraceProduct_fundamentalDomain_of_primitiveRoot K hζ]
    exact ENNReal.one_ne_top
  have hconst : IntegrableOn (fun _ : 𝔸[K] =>
      sourceKPAdelicCompactScalar K hζ s g + sourceKPAdelicTraceIntertwiner K hζ s g)
      (sourceKPAdelicFundamentalDomain K) (sourceKPAdelicTraceProduct K) := integrableOn_const hm
  apply ((sourceKPAdelicCompactEisenstein_trace_integrable K hζ hs g).sub hconst).congr
  exact Eventually.of_forall (fun y => (sourceKPAdelicNonconstantEisenstein_upper K hζ s g y).symm)

theorem sourceKPAdelicNonconstantEisenstein_trace_mean_zero {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (g : SourceKPAdelicProjective K hζ) :
    (∫ y in sourceKPAdelicFundamentalDomain K,
      sourceKPAdelicNonconstantEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y * g)
        ∂sourceKPAdelicTraceProduct K) = 0 := by
  have hm : sourceKPAdelicTraceProduct K (sourceKPAdelicFundamentalDomain K) ≠ ⊤ := by
    rw [sourceKPAdelicTraceProduct_fundamentalDomain_of_primitiveRoot K hζ]
    exact ENNReal.one_ne_top
  have hconst : IntegrableOn (fun _ : 𝔸[K] =>
      sourceKPAdelicCompactScalar K hζ s g + sourceKPAdelicTraceIntertwiner K hζ s g)
      (sourceKPAdelicFundamentalDomain K) (sourceKPAdelicTraceProduct K) := integrableOn_const hm
  calc
    _ = ∫ y in sourceKPAdelicFundamentalDomain K,
        sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y * g) -
          (sourceKPAdelicCompactScalar K hζ s g + sourceKPAdelicTraceIntertwiner K hζ s g)
            ∂sourceKPAdelicTraceProduct K := by
      apply integral_congr_ae
      exact Eventually.of_forall (sourceKPAdelicNonconstantEisenstein_upper K hζ s g)
    _ = _ := by
      rw [integral_sub (sourceKPAdelicCompactEisenstein_trace_integrable K hζ hs g) hconst,
        sourceKPAdelicCompactEisenstein_traceConstantTerm K hζ hs g, setIntegral_const,
        Measure.real, sourceKPAdelicTraceProduct_fundamentalDomain_of_primitiveRoot K hζ,
        ENNReal.toReal_one, one_smul, sub_self]

end
end ArtinMatthews
