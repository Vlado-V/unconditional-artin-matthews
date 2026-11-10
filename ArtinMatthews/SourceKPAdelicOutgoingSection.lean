module

public import ArtinMatthews.SourceKPAdelicCoordinateIntertwiner
public import ArtinMatthews.SourceKPAdelicTraceConstantTerm
public import ArtinMatthews.SourceKPAdelicCoordinateParameter
public import ArtinMatthews.SourceKPAdelicOutgoingTorus
public import ArtinMatthews.SourceKPAdelicOutgoingTranslation
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

/-! The literal measured standard operator is a section of the actual
negative-parameter induced space. The coarse initial half-plane gives
absolute integrability in every torus coordinate. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "A" => 𝔸[K]
local notation "G" => SourceKPAdelicProjective K hζ
local notation "T" => sourceKPAdelicCoveringTorus K hζ
local notation "B" => sourceKPAdelicCoveringBorel K hζ
local notation "D" => sourceKPAdelicDeepCompact K hζ
local notation "M" => sourceKPAdelicSphericalIntertwinerValue K hζ (sourceKPAdelicTraceProduct K)
local notation "ρ" => sourceKPAdelicNormalizedBorelRepresentation K hζ
local notation "τ" => sourceKPAdelicTorusInducedRepresentation K hζ
local notation "d₀" => sourceKPAdelicBorelTorusInclusion K hζ
local notation "δ" => sourceKPAdelicBorelModularHalf K hζ
local notation "p" => sourceKPAdelicBorelTorusProjection K hζ

local instance sourceKPAdelicOutgoingSectionMeasurable : MeasurableSpace A := borel A
local instance sourceKPAdelicOutgoingSectionBorel : BorelSpace A := ⟨rfl⟩

theorem sourceKPAdelicOutgoingValue_borel (s : ℂ) (b : B) (g : G) :
    M s (b.val*g) = ρ (-s) b (M s g) := by
  obtain ⟨x,t,hxt⟩ := (sourceKPAdelicCoveringBorel_mem_iff K hζ b.val).mp b.property
  have hb : p b = t := by
    have h : b = sourceKPAdelicBorelCoordinatesEquiv K hζ (x,t) := Subtype.ext hxt
    rw [h,sourceKPAdelicBorelTorusProjection_coordinates]
  have hδ : δ b = δ (d₀ t) := by
    change (sourceKPIdeleComplexNorm K (1/2 : ℂ) (sourceKPAdelicTorusIdele K hζ (p b)) : ℂ) =
      (sourceKPIdeleComplexNorm K (1/2 : ℂ) (sourceKPAdelicTorusIdele K hζ (p (d₀ t))) : ℂ)
    rw [hb,sourceKPAdelicBorelTorusProjection_inclusion]
  rw [hxt,mul_assoc,sourceKPAdelicOutgoingValue_upper K hζ,
    sourceKPAdelicOutgoingValue_torus K hζ]
  change δ (d₀ t) • τ (-s) (p (d₀ t)) (M s g) = δ b • τ (-s) (p b) (M s g)
  rw [hb,hδ,sourceKPAdelicBorelTorusProjection_inclusion]

def sourceKPAdelicOutgoingSection (s : ℂ) : SourceKPAdelicPrincipalSeries K hζ (-s) :=
  ⟨M s,sourceKPAdelicOutgoingValue_borel K hζ s⟩

theorem sourceKPAdelicOutgoingSection_apply (s : ℂ) (g : G) :
    (sourceKPAdelicOutgoingSection K hζ s).val g = M s g := rfl

theorem sourceKPAdelicOutgoingSection_right (s : ℂ) (k : D) :
    sourceKPAdelicPrincipalSeriesRepresentation K hζ (-s) k.val
      (sourceKPAdelicOutgoingSection K hζ s) = sourceKPAdelicOutgoingSection K hζ s := by
  apply Subtype.ext
  funext g
  exact sourceKPAdelicOutgoingValue_deep_right K hζ s g k

theorem sourceKPAdelicOutgoingSection_trace_one (s : ℂ) (g : G) :
    ((sourceKPAdelicOutgoingSection K hζ s).val g).val 1 =
      sourceKPAdelicTraceIntertwiner K hζ s g :=
  sourceKPAdelicSphericalIntertwinerValue_trace_one K hζ s g

theorem sourceKPAdelicOutgoingSection_coordinate_integrable
    {s : ℂ} (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (g : G) (t : T) :
    Integrable (sourceKPAdelicCoordinateKernel K hζ s g (sourceKPAdelicCoveringTorusWeyl K hζ t))
      (sourceKPAdelicTraceProduct K) :=
  sourceKPAdelicSphericalIntertwinerValue_trace_integrable K hζ hs g t

end
end ArtinMatthews
