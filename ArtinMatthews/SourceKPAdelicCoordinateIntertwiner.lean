module

public import ArtinMatthews.SourceKPAdelicTorusWeylTransport
public import ArtinMatthews.SourceKPAdelicConstantTermPeriodization
public import ArtinMatthews.SourceKPAdelicCoordinateKernel
public import ArtinMatthews.SourceKPAdelicCoordinateIntegrable
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

/-! Coordinatewise integration gives a value in the actual algebraic
induced torus carrier. Weyl transport places it in parameter -s. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPCoordinateValueMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPCoordinateValueBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

theorem sourceKPAdelicCoordinateKernel_covariant (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (h : sourceKPAdelicTorusInducingSubgroup K hζ)
    (t : sourceKPAdelicCoveringTorus K hζ) (y : 𝔸[K]) :
    sourceKPAdelicCoordinateKernel K hζ s g (h.val*t) y =
      (sourceKPAdelicTorusInducingCharacter K hζ s h : ℂ) *
        sourceKPAdelicCoordinateKernel K hζ s g t y :=
  (((sourceKPAdelicCompactSection K hζ s).val
    (sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ y * g)).property h t)

def sourceKPAdelicCoordinateIntegral (μ : Measure 𝔸[K]) (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) : SourceKPAdelicTorusInducedSpace K hζ s :=
  ⟨fun t => ∫ y, sourceKPAdelicCoordinateKernel K hζ s g t y ∂μ, by
    intro h t
    change (∫ y, sourceKPAdelicCoordinateKernel K hζ s g (h.val*t) y ∂μ) =
      (sourceKPAdelicTorusInducingCharacter K hζ s h : ℂ) *
        ∫ y, sourceKPAdelicCoordinateKernel K hζ s g t y ∂μ
    simp_rw [sourceKPAdelicCoordinateKernel_covariant]
    exact integral_const_mul _ _⟩

theorem sourceKPAdelicCoordinateIntegral_apply (μ : Measure 𝔸[K]) (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) :
    (sourceKPAdelicCoordinateIntegral K hζ μ s g).val t =
      ∫ y, sourceKPAdelicCoordinateKernel K hζ s g t y ∂μ := rfl

def sourceKPAdelicSphericalIntertwinerValue (μ : Measure 𝔸[K]) (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) : SourceKPAdelicTorusInducedSpace K hζ (-s) :=
  sourceKPAdelicTorusWeylTransport K hζ s (sourceKPAdelicCoordinateIntegral K hζ μ s g)

theorem sourceKPAdelicSphericalIntertwinerValue_apply (μ : Measure 𝔸[K]) (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) :
    (sourceKPAdelicSphericalIntertwinerValue K hζ μ s g).val t =
      ∫ y, sourceKPAdelicCoordinateKernel K hζ s g (sourceKPAdelicCoveringTorusWeyl K hζ t) y ∂μ := rfl

theorem sourceKPAdelicSphericalIntertwinerValue_integrable (μ : Measure 𝔸[K]) [μ.IsAddHaarMeasure]
    {s : ℂ} (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : SourceKPAdelicProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ) :
    Integrable (sourceKPAdelicCoordinateKernel K hζ s g (sourceKPAdelicCoveringTorusWeyl K hζ t)) μ :=
  sourceKPAdelicCoordinateKernel_integrable K hζ μ hs g _

theorem sourceKPAdelicSphericalIntertwinerValue_one (μ : Measure 𝔸[K]) (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) :
    (sourceKPAdelicSphericalIntertwinerValue K hζ μ s g).val 1 =
      ∫ y, sourceKPAdelicIntertwiningKernel K hζ s g y ∂μ := by
  rw [sourceKPAdelicSphericalIntertwinerValue_apply, map_one]
  rfl

theorem sourceKPAdelicSphericalIntertwinerValue_covariant (μ : Measure 𝔸[K]) (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (h : sourceKPAdelicTorusInducingSubgroup K hζ)
    (t : sourceKPAdelicCoveringTorus K hζ) :
    (sourceKPAdelicSphericalIntertwinerValue K hζ μ s g).val (h.val*t) =
      (sourceKPAdelicTorusInducingCharacter K hζ (-s) h : ℂ) *
        (sourceKPAdelicSphericalIntertwinerValue K hζ μ s g).val t :=
  (sourceKPAdelicSphericalIntertwinerValue K hζ μ s g).property h t

end
end ArtinMatthews
