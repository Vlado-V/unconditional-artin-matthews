module

public import ArtinMatthews.SourceKPCuspLevelTopology
public import ArtinMatthews.SourceKPCuspTraceHaar
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import ArtinMatthews.SourceKPCuspPoincare
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
public import Mathlib.NumberTheory.Height.NumberField
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

/-! The trace-normalized probability and Poincare estimate for genuine functions
    on the original automorphic level, pulled back through its principal cusp cover. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Module Module.Free MeasureTheory Topology
open scoped NumberField AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (g : SourceKPAdelicProjective K hζ)
local notation "E" => mixedEmbedding.mixedSpace K
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "X" => SourceKPAutomorphicLevel K hζ

def sourceKPCuspChosenPeriod : 𝓞 K :=
  (sourceKPAdelicCuspFiniteLevelPeriod K hζ g).choose

lemma sourceKPCuspChosenPeriod_ne_zero : sourceKPCuspChosenPeriod K hζ g ≠ 0 :=
  (sourceKPAdelicCuspFiniteLevelPeriod K hζ g).choose_spec.1

lemma sourceKPCuspChosenPeriod_stabilizes :
    ∀ t ∈ sourceKPCuspFiniteIdeal K (sourceKPCuspChosenPeriod K hζ g),
      ∃ k : sourceKPFiniteDeepMatrixGroup K,
        g⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * g =
          sourceKPFiniteDeepCoverLift K hζ k :=
  (sourceKPAdelicCuspFiniteLevelPeriod K hζ g).choose_spec.2

local notation "D" => sourceKPCuspChosenPeriod K hζ g
local notation "Q" => SourceKPCuspPrincipalQuotient K D
local instance : MeasurableSpace Q := borel Q
local instance : BorelSpace Q := ⟨rfl⟩
local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

def sourceKPCuspChosenCover : C(Q, X) :=
  sourceKPCuspLevelCoverContinuous K hζ D g
    (sourceKPCuspChosenPeriod_stabilizes K hζ g) (sourceKPCuspChosenPeriod_ne_zero K hζ g)

lemma sourceKPCuspChosenCover_arch (x : E) :
    sourceKPCuspChosenCover K hζ g (sourceKPCuspArchQuotientMap K D x) =
      sourceKPCuspOrbit K hζ g
        (OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction.mixedAdelicAdd K x) := rfl

def sourceKPCuspLevelTraceProbability : Measure X :=
  Measure.map (sourceKPCuspChosenCover K hζ g) (sourceKPCuspTraceHaar K D)

lemma sourceKPCuspLevelTraceProbability_probability :
    IsProbabilityMeasure (sourceKPCuspLevelTraceProbability K hζ g) := by
  let : IsProbabilityMeasure (sourceKPCuspTraceHaar K D) := sourceKPCuspTraceHaar_probability K D hζ
  exact (Measure.isProbabilityMeasure_map_iff
    (sourceKPCuspChosenCover K hζ g).continuous.measurable.aemeasurable).mpr inferInstance

lemma sourceKPCuspLevelTraceProbability_integral (f : C(X, ℂ)) :
    (∫ x, f x ∂sourceKPCuspLevelTraceProbability K hζ g) =
      ∫ q, f (sourceKPCuspChosenCover K hζ g q) ∂sourceKPCuspTraceHaar K D :=
  integral_map_of_stronglyMeasurable
    (sourceKPCuspChosenCover K hζ g).continuous.measurable f.continuous.stronglyMeasurable

lemma sourceKPCuspLevelTraceProbability_integral_norm (f : C(X, ℂ)) :
    (∫ x, ‖f x‖ ^ 2 ∂sourceKPCuspLevelTraceProbability K hζ g) =
      ∫ q, ‖f (sourceKPCuspChosenCover K hζ g q)‖ ^ 2 ∂sourceKPCuspTraceHaar K D :=
  integral_map_of_stronglyMeasurable
    (sourceKPCuspChosenCover K hζ g).continuous.measurable (f.continuous.norm.pow 2).stronglyMeasurable

theorem sourceKPCuspLevel_poincare (f : C(X, ℂ)) (derivatives : I → C(X, ℂ))
    (hderiv : ∀ (i : I) (x : E) (t : ℝ),
      HasDerivAt
        (fun u : ℝ => f (sourceKPCuspOrbit K hζ g
          (OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction.mixedAdelicAdd K
            (x + u • sourceKPCuspLatticeBasis K D (sourceKPCuspChosenPeriod_ne_zero K hζ g) i))))
        (derivatives i (sourceKPCuspOrbit K hζ g
          (OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction.mixedAdelicAdd K
            (x + t • sourceKPCuspLatticeBasis K D (sourceKPCuspChosenPeriod_ne_zero K hζ g) i)))) t)
    (hmean : (∫ x, f x ∂sourceKPCuspLevelTraceProbability K hζ g) = 0) :
    (2 * Real.pi) ^ 2 * (∫ x, ‖f x‖ ^ 2 ∂sourceKPCuspLevelTraceProbability K hζ g) ≤
      ∑ i, ∫ x, ‖derivatives i x‖ ^ 2 ∂sourceKPCuspLevelTraceProbability K hζ g := by
  let F : C(Q, ℂ) := f.comp (sourceKPCuspChosenCover K hζ g)
  let G : I → C(Q, ℂ) := fun i => (derivatives i).comp (sourceKPCuspChosenCover K hζ g)
  have hFG : SourceKPCuspDirectionalDerivative K D
      (sourceKPCuspChosenPeriod_ne_zero K hζ g) F G := by
    intro i x t
    simpa only [F, G, ContinuousMap.comp_apply, sourceKPCuspChosenCover_arch] using hderiv i x t
  have hF : (∫ q, F q ∂sourceKPCuspTraceHaar K D) = 0 :=
    (sourceKPCuspLevelTraceProbability_integral K hζ g f).symm.trans hmean
  simpa only [F, G, ContinuousMap.comp_apply,
    ← sourceKPCuspLevelTraceProbability_integral_norm] using
    sourceKPCusp_directional_poincare K D (sourceKPCuspChosenPeriod_ne_zero K hζ g) hζ F G hFG hF

end
end ArtinMatthews
