module

public import ArtinMatthews.SourceArchSectionFactorization
public import ArtinMatthews.SourceKPAdelicTraceConstantTerm
public import ArtinMatthews.SourceIntertwinerProductMeasure
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

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance archFiniteAdelicMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance archFiniteAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance archFiniteFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance archFiniteFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance archFiniteCompletionMeasurable (v : InfinitePlace K) : MeasurableSpace v.Completion := borel _
local instance archFiniteCompletionBorel (v : InfinitePlace K) : BorelSpace v.Completion := ⟨rfl⟩
local instance archFiniteInfiniteMeasurable : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ v : InfinitePlace K, v.Completion))

def sourceKPArchIntertwiningKernel (s : ℂ) (g : PGL(2, InfiniteAdeleRing K))
    (x : InfiniteAdeleRing K) : ℂ :=
  sourceArchSphericalProduct K hζ s
    ((sourceKPAdelicProjectiveWeyl K hζ).1 *
      ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) x) * g)

def sourceKPFiniteIntertwiningKernel (s : ℂ) (g : SourceKPFiniteAdeleProjective K hζ)
    (x : 𝔸ᶠ[K]) : ℂ :=
  sourceKPAdelicCompactScalar K hζ s
    (1, (sourceKPAdelicProjectiveWeyl K hζ).2 * sourceKPFiniteAdeleUpperLift K hζ x * g)

theorem sourceKPAdelicIntertwiningKernel_arch_finite (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) :
    sourceKPAdelicIntertwiningKernel K hζ s g y =
      sourceKPArchIntertwiningKernel K hζ s g.1 y.1 *
        sourceKPFiniteIntertwiningKernel K hζ s g.2 y.2 := by
  change sourceKPAdelicCompactScalar K hζ s
    ((sourceKPAdelicProjectiveWeyl K hζ).1 *
      ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) y.1) * g.1,
     (sourceKPAdelicProjectiveWeyl K hζ).2 * sourceKPFiniteAdeleUpperLift K hζ y.2 * g.2) = _
  exact sourceArchCompactScalar_factor K hζ s _ _

def sourceKPArchIntertwiner (s : ℂ) (g : PGL(2, InfiniteAdeleRing K)) : ℂ :=
  ∫ x, sourceKPArchIntertwiningKernel K hζ s g x ∂sourceKPArchSelfDualProduct K

def sourceKPFiniteIntertwiner (s : ℂ) (g : SourceKPFiniteAdeleProjective K hζ) : ℂ :=
  ∫ x, sourceKPFiniteIntertwiningKernel K hζ s g x ∂sourceKPFiniteStandardHaar K

theorem sourceKPAdelicTraceIntertwiner_arch_finite (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicTraceIntertwiner K hζ s g =
      sourceKPArchIntertwiner K hζ s g.1 * sourceKPFiniteIntertwiner K hζ s g.2 := by
  unfold sourceKPAdelicTraceIntertwiner sourceKPAdelicIntertwiner
  simp_rw [sourceKPAdelicIntertwiningKernel_arch_finite]
  exact sourceKPTraceProduct_integral_separated K hζ _ _

end
end ArtinMatthews
