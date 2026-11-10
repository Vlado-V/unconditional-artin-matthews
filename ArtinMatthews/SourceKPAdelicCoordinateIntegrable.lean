module

public import ArtinMatthews.SourceKPAdelicCoordinateKernel
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

/-! Every torus coordinate of the spherical-section intertwining
kernel is absolutely integrable in the proved initial half-plane. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPCoordinateMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPCoordinateBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

theorem sourceKPAdelicCoordinateKernel_eq_kernel (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) (y : 𝔸[K]) :
    sourceKPAdelicCoordinateKernel K hζ s g t y =
      (sourceKPAdelicBorelModularHalf K hζ (sourceKPAdelicBorelTorusInclusion K hζ t))⁻¹ *
        sourceKPAdelicIntertwiningKernel K hζ s ((sourceKPAdelicCoveringTorusWeyl K hζ t).val * g)
          ((sourceKPAdelicTorusIdele K hζ (sourceKPAdelicCoveringTorusWeyl K hζ t) : 𝔸[K]) * y) :=
  sourceKPAdelicCoordinateKernel_eq_scalar K hζ s g t y

theorem sourceKPAdelicCoordinateKernel_continuous (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) :
    Continuous (sourceKPAdelicCoordinateKernel K hζ s g t) := by
  change Continuous (fun y : 𝔸[K] => sourceKPAdelicCoordinateKernel K hζ s g t y)
  simp_rw [sourceKPAdelicCoordinateKernel_eq_kernel]
  exact continuous_const.mul
    ((sourceKPAdelicIntertwiningKernel_continuous K hζ s _).comp (continuous_const_mul _))

theorem sourceKPAdelicCoordinateKernel_integrable (μ : Measure 𝔸[K]) [μ.IsAddHaarMeasure]
    {s : ℂ} (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) :
    Integrable (sourceKPAdelicCoordinateKernel K hζ s g t) μ := by
  let a := sourceKPAdelicTorusIdele K hζ (sourceKPAdelicCoveringTorusWeyl K hζ t)
  let e : 𝔸[K] ≃ₜ+ 𝔸[K] := ContinuousAddEquiv.mulLeft a
  have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have hkernel := sourceKPAdelicIntertwiningKernel_integrable K hζ (μ.map e) hs
    ((sourceKPAdelicCoveringTorusWeyl K hζ t).val * g)
  have hcomp := hkernel.comp_measurable e.continuous.measurable
  have hscaled := hcomp.const_mul
    ((sourceKPAdelicBorelModularHalf K hζ (sourceKPAdelicBorelTorusInclusion K hζ t))⁻¹)
  apply hscaled.congr
  exact Filter.Eventually.of_forall (fun y => (sourceKPAdelicCoordinateKernel_eq_kernel K hζ s g t y).symm)

end
end ArtinMatthews
