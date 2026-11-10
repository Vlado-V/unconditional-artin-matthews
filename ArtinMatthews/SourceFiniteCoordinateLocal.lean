module

public import ArtinMatthews.SourceCoordinateIntertwinerProduct
public import ArtinMatthews.SourceKPExteriorScattering
public import ArtinMatthews.SourceKPExteriorUpperCompatibility
public import ArtinMatthews.SourceKPLocalRestCommute
public import ArtinMatthews.SourceCoordinateFiberReduction
public import ArtinMatthews.SourceKPLocalFiberIntegral
public import ArtinMatthews.StandardLocalBall
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

open NumberField IsDedekindDomain MeasureTheory StandardAdelic
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance finiteCoordinateLocalCompletionMeasurable (P : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (P.adicCompletion K) := borel _
local instance finiteCoordinateLocalCompletionBorel (P : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (P.adicCompletion K) := ⟨rfl⟩

theorem sourceKPFiniteCoordinateFiber_relation
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)
    (s : ℂ) (g : SourceKPFiniteAdeleProjective K hζ)
    (hg : sourceKPAdelicLocalBase K hζ P.val (1, g) = 1)
    (t : sourceKPAdelicCoveringTorus K hζ) (r : 𝔸ᶠ[K]) (hr : r P.val = 0)
    (hP : P.val ∉ traceBadPlaces K) (hs : 0 < s.re) :
    (∫ x : P.val.adicCompletion K,
      sourceKPFiniteCoordinateIntertwiningKernel K hζ s g t.val.2
        (sourceKPFiniteAdditiveSingle K P.val x + r) ∂sourceJacquetHaar K P.val) =
      sourceKPUnramifiedScatteringFactor P.val s *
        ∫ x : P.val.adicCompletion K in (P.val.adicCompletionIntegers K : Set _),
          sourceKPFiniteCoordinateIntertwiningKernel K hζ s g t.val.2
            (sourceKPFiniteAdditiveSingle K P.val x + r) ∂sourceJacquetHaar K P.val := by
  apply sourceKPFiniteCoordinateFiber_relation_of_global K hζ P.val s g t r
    (sourceKPUnramifiedScatteringFactor P.val s)
  simpa only [sourceKPAdelicCoordinateKernel, SourcePhysical.sourceLocalBall_zero] using
    sourceKPLocalFiber_integral_eq_factor_unit_ball K hζ S₀ P s r hr (1, g) hg t hP hs

end
end ArtinMatthews
