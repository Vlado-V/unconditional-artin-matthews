module

public import ArtinMatthews.SourceKPAdelicCoordinateIntertwiner
public import ArtinMatthews.SourceKPAdelicTraceConstantTerm
public import ArtinMatthews.SourceKPAdelicCoordinateIntegrable
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

/-! The coordinatewise value agrees with the actual scalar integral
under a pushed-forward Haar measure and is holomorphic in the proved
initial half-plane. The trace-self-dual normalization is retained. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPCoordinateParameterMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPCoordinateParameterBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

theorem sourceKPAdelicCoordinateIntegral_eq_intertwiner (μ : Measure 𝔸[K]) (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) :
    (sourceKPAdelicCoordinateIntegral K hζ μ s g).val t =
      (sourceKPAdelicBorelModularHalf K hζ (sourceKPAdelicBorelTorusInclusion K hζ t))⁻¹ *
        sourceKPAdelicIntertwiner K hζ
          (μ.map (fun y : 𝔸[K] =>
            (sourceKPAdelicTorusIdele K hζ (sourceKPAdelicCoveringTorusWeyl K hζ t) : 𝔸[K]) * y))
          s ((sourceKPAdelicCoveringTorusWeyl K hζ t).val * g) := by
  rw [sourceKPAdelicCoordinateIntegral_apply]
  simp_rw [sourceKPAdelicCoordinateKernel_eq_kernel]
  rw [integral_const_mul]
  congr 1
  exact (integral_map (continuous_const_mul _).measurable.aemeasurable
    (sourceKPAdelicIntertwiningKernel_aestronglyMeasurable K hζ _ s _)).symm

theorem sourceKPAdelicCoordinateIntegral_holomorphic (μ : Measure 𝔸[K]) [μ.IsAddHaarMeasure]
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) :
    DifferentiableOn ℂ (fun s => (sourceKPAdelicCoordinateIntegral K hζ μ s g).val t)
      {s : ℂ | ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) < 2*s.re+1} := by
  let a := sourceKPAdelicTorusIdele K hζ (sourceKPAdelicCoveringTorusWeyl K hζ t)
  let e : 𝔸[K] ≃ₜ+ 𝔸[K] := ContinuousAddEquiv.mulLeft a
  have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  simp_rw [sourceKPAdelicCoordinateIntegral_eq_intertwiner]
  apply DifferentiableOn.mul
  · exact differentiableOn_const
      ((sourceKPAdelicBorelModularHalf K hζ (sourceKPAdelicBorelTorusInclusion K hζ t))⁻¹)
  · exact sourceKPAdelicIntertwiner_holomorphic K hζ (μ.map e)
      ((sourceKPAdelicCoveringTorusWeyl K hζ t).val * g)

theorem sourceKPAdelicSphericalIntertwinerValue_holomorphic (μ : Measure 𝔸[K]) [μ.IsAddHaarMeasure]
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) :
    DifferentiableOn ℂ (fun s => (sourceKPAdelicSphericalIntertwinerValue K hζ μ s g).val t)
      {s : ℂ | ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) < 2*s.re+1} :=
  sourceKPAdelicCoordinateIntegral_holomorphic K hζ μ g (sourceKPAdelicCoveringTorusWeyl K hζ t)

theorem sourceKPAdelicSphericalIntertwinerValue_trace_one (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) :
    (sourceKPAdelicSphericalIntertwinerValue K hζ (sourceKPAdelicTraceProduct K) s g).val 1 =
      sourceKPAdelicTraceIntertwiner K hζ s g :=
  sourceKPAdelicSphericalIntertwinerValue_one K hζ (sourceKPAdelicTraceProduct K) s g

theorem sourceKPAdelicSphericalIntertwinerValue_trace_integrable
    {s : ℂ} (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) :
    Integrable (sourceKPAdelicCoordinateKernel K hζ s g (sourceKPAdelicCoveringTorusWeyl K hζ t))
      (sourceKPAdelicTraceProduct K) := by
  rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
  exact sourceKPAdelicSphericalIntertwinerValue_integrable K hζ (sourceKPAdelicStandardHaar K) hs g t

end
end ArtinMatthews
