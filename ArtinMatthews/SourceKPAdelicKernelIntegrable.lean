module

public import ArtinMatthews.SourceAdelicHaarUnfolding
public import ArtinMatthews.SourceKPAdelicConstantTermPeriodization
public import ArtinMatthews.SourceKPAdelicKernelCompactBound
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

/-! The quantitative compact-domain bound gives global L1 once the
actual kernel's spatial measurability has been established. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing Topology ENNReal BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPKernelIntegrableMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPKernelIntegrableBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

theorem sourceKPAdelicIntertwiningKernel_integrable_of_aestronglyMeasurable
    (μ : Measure 𝔸[K]) [μ.IsAddHaarMeasure] {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ)
    (hf : AEStronglyMeasurable (sourceKPAdelicIntertwiningKernel K hζ s g) μ) :
    Integrable (sourceKPAdelicIntertwiningKernel K hζ s g) μ := by
  obtain ⟨B,_hB,hbound⟩ := sourceKPAdelicIntertwiningKernel_compact_sum_bound K hζ hs g
    (CompactQuotient.Construction.adelicCompactRepresentatives K)
    (CompactQuotient.Construction.isCompact_adelicCompactRepresentatives K)
  apply sourceKPAdelicIntegrable_of_periodization K μ _ hf
  let M := B * ∑' x : K, Height.mulHeight₁ x ^ (-(2*s.re+1))
  have hpoint (a : 𝔸[K]) (ha : a ∈ sourceKPAdelicFundamentalDomain K) :
      (∑' x : K, ENNReal.ofReal ‖sourceKPAdelicIntertwiningKernel K hζ s g
        (a+algebraMap K 𝔸[K] x)‖) ≤ ENNReal.ofReal M := by
    have he (x : K) : a+algebraMap K 𝔸[K] x = algebraMap K 𝔸[K] x+a := add_comm _ _
    simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _)
      (sourceKPAdelicIntertwiningKernel_periodization_summable K hζ hs g a).norm]
    apply ENNReal.ofReal_le_ofReal
    exact hbound a (sourceKPAdelicFundamentalDomain_subset_compact K ha)
  have hle : (∫⁻ a in sourceKPAdelicFundamentalDomain K,
      ∑' x : K, ENNReal.ofReal ‖sourceKPAdelicIntertwiningKernel K hζ s g
        (a+algebraMap K 𝔸[K] x)‖ ∂μ) ≤
      ∫⁻ _a in sourceKPAdelicFundamentalDomain K, ENNReal.ofReal M ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (sourceKPAdelicFundamentalDomain_measurable K)] with a ha
    exact hpoint a ha
  apply hle.trans_lt
  rw [lintegral_const]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  simpa using sourceKPAdelicFundamentalDomain_measure_lt_top K μ

theorem sourceKPAdelicConstantTerm_integral_of_aestronglyMeasurable
    (μ : Measure 𝔸[K]) [μ.IsAddHaarMeasure] {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ)
    (hf : AEStronglyMeasurable (sourceKPAdelicIntertwiningKernel K hζ s g) μ) :
    (∫ y in sourceKPAdelicFundamentalDomain K,
      sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y*g) ∂μ) =
        μ.real (sourceKPAdelicFundamentalDomain K) • sourceKPAdelicCompactScalar K hζ s g +
          ∫ y, sourceKPAdelicIntertwiningKernel K hζ s g y ∂μ := by
  let F := sourceKPAdelicIntertwiningKernel K hζ s g
  have hF : Integrable F μ := sourceKPAdelicIntertwiningKernel_integrable_of_aestronglyMeasurable K hζ μ hs g hf
  have hP := sourceKPAdelicPeriodization_integrable K μ F hF
  have hC : IntegrableOn (fun _ : 𝔸[K] => sourceKPAdelicCompactScalar K hζ s g)
      (sourceKPAdelicFundamentalDomain K) μ :=
    integrableOn_const (sourceKPAdelicFundamentalDomain_measure_lt_top K μ).ne
  have he (y : 𝔸[K]) :
      sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y*g) =
        sourceKPAdelicCompactScalar K hζ s g + sourceKPAdelicPeriodization K F y := by
    rw [sourceKPAdelicCompactEisenstein_upper_periodization K hζ hs g y,
      sourceKPAdelicPeriodization]
    congr 1
    apply tsum_congr
    intro x
    exact congrArg F (add_comm _ _)
  calc
    _ = ∫ y in sourceKPAdelicFundamentalDomain K,
        (sourceKPAdelicCompactScalar K hζ s g + sourceKPAdelicPeriodization K F y) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall he
    _ = (∫ _y in sourceKPAdelicFundamentalDomain K, sourceKPAdelicCompactScalar K hζ s g ∂μ) +
        ∫ y in sourceKPAdelicFundamentalDomain K, sourceKPAdelicPeriodization K F y ∂μ :=
      integral_add hC hP
    _ = _ := by rw [setIntegral_const, sourceKPAdelicHaarUnfolding K μ F hF]

end
end ArtinMatthews
