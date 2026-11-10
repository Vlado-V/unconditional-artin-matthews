module

public import ArtinMatthews.SourceFiniteWindowEuler
public import ArtinMatthews.SourceCoordinateIntertwinerProduct
public import ArtinMatthews.SourceFiniteIntertwinerFubini
public import ArtinMatthews.SourceFiniteProjectiveSupport
public import ArtinMatthews.SourceFiniteSupportedFiber
public import ArtinMatthews.SourceFiniteWindowStep
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
open scoped NumberField AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance actualEulerFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel _
local instance actualEulerFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance actualEulerCompletionMeasurable (P : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (P.adicCompletion K) := borel _
local instance actualEulerCompletionBorel (P : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (P.adicCompletion K) := ⟨rfl⟩

theorem sourceKPInitialHalfplane_exterior {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1) :
    1 / 6 < s.re := by
  have hn : (0 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
  push_cast at hs
  linarith

theorem sourceKPFiniteCoordinateIntertwiner_eq_euler
    (g : SourceKPFiniteAdeleProjective K hζ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      S₀ ⊆ S ∧ sourceHilbertSet K ∅ ⊆ S ∧ traceBadPlaces K ⊆ S ∧
      ∀ (s : ℂ), ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1 →
        ∀ t : sourceKPAdelicCoveringTorus K hζ,
          sourceKPFiniteCoordinateIntertwiner K hζ s g t.val.2 =
            sourceKPExteriorScattering S s *
              sourceKPFiniteWindowIntegral K
                (sourceKPFiniteCoordinateIntertwiningKernel K hζ s g t.val.2) S := by
  obtain ⟨a, S, ha, hS, hbad, hcompact⟩ :=
    sourceKPFiniteProjective_support_compact K hζ g (S₀ ∪ sourceHilbertSet K ∅)
  refine ⟨S, Finset.subset_union_left.trans hS, Finset.subset_union_right.trans hS,
    hbad, ?_⟩
  intro s hs t
  have hex := sourceKPInitialHalfplane_exterior K hs
  have hpos : 0 < s.re := lt_trans (by norm_num) hex
  have hf := sourceKPFiniteCoordinateIntertwiningKernel_integrable K hζ hs (1, g) t
  apply sourceKPFiniteWindowIntegral_eq_product_limit K S _ hf
    (fun P => sourceKPUnramifiedScatteringFactor P s) _
    (sourceKPUnramifiedScatteringFactor_hasProd_all K S hex)
  intro T P hPT hPS
  apply sourceKPFiniteWindow_integral_step K T P hPT _ hf
  intro r _
  have hHilbert : P ∉ sourceHilbertSet K ∅ := fun h =>
    hPS (hS (Finset.mem_union_right _ h))
  let P' : SourceExteriorPrime K ∅ := ⟨P, hHilbert⟩
  obtain ⟨h6, k, hk⟩ := hcompact P hPS
  have hpbad : P ∉ traceBadPlaces K := fun h => hPS (hbad h)
  have hlocal := sourceKPFiniteCoordinateFiber_of_integral_representative K hζ
    P' h6 a k hk s t r.val r.property hpbad hpos
  simpa only [ha] using hlocal

end
end ArtinMatthews
