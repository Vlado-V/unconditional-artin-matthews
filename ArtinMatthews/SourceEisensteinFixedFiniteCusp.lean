module

public import ArtinMatthews.SourceEisensteinNonconstant
public import ArtinMatthews.SourceKPAutomorphicEisenstein
public import ArtinMatthews.SourceKPCuspLevelPoincare
public import ArtinMatthews.SourceKPCuspSobolev
public import ArtinMatthews.SourceEisensteinUpperContinuity
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

/-! The genuine principal cusp period can be fixed on an entire finite fiber.
The resulting trace-Haar torus and its zero-mean remainder are independent of
archimedean height and shape in that fiber. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPFixedFiniteCuspPeriod (qf : SourceKPFiniteAdeleProjective K hζ) : 𝓞 K :=
  sourceKPCuspChosenPeriod K hζ (1,qf)

theorem sourceKPFixedFiniteCuspPeriod_ne_zero (qf : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPFixedFiniteCuspPeriod K hζ qf ≠ 0 := sourceKPCuspChosenPeriod_ne_zero K hζ (1,qf)

theorem sourceKPFixedFiniteCuspPeriod_stabilizes (qf : SourceKPFiniteAdeleProjective K hζ)
    (a : PGL(2,InfiniteAdeleRing K)) (t : 𝔸ᶠ[K])
    (ht : t ∈ sourceKPCuspFiniteIdeal K (sourceKPFixedFiniteCuspPeriod K hζ qf)) :
    ∃ k : sourceKPFiniteDeepMatrixGroup K,
      (a,qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (a,qf) =
        sourceKPFiniteDeepCoverLift K hζ k := by
  obtain ⟨k,hk⟩ := sourceKPCuspChosenPeriod_stabilizes K hζ (1,qf) t ht
  refine ⟨k,?_⟩
  have he : (a,qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (a,qf) =
      ((1,qf) : SourceKPAdelicProjective K hζ)⁻¹ *
        sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (1,qf) := by
    apply Prod.ext
    · change a⁻¹ * (sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t)).1 * a =
        1⁻¹ * (sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t)).1 * 1
      rw [sourceKPAdelicUpperLift_finite_fst]
      group
    · rfl
  exact he.trans hk

variable (qf : SourceKPFiniteAdeleProjective K hζ)
local notation "D" => sourceKPFixedFiniteCuspPeriod K hζ qf
local notation "Q" => SourceKPCuspPrincipalQuotient K D
local instance sourceFixedCuspAdelicMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceFixedCuspAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance sourceFixedCuspQuotientMeasurable : MeasurableSpace Q := borel Q
local instance sourceFixedCuspQuotientBorel : BorelSpace Q := ⟨rfl⟩

def sourceKPFixedFiniteCuspCover (a : PGL(2,InfiniteAdeleRing K)) :
    C(Q,SourceKPAutomorphicLevel K hζ) :=
  sourceKPCuspLevelCoverContinuous K hζ D (a,qf)
    (sourceKPFixedFiniteCuspPeriod_stabilizes K hζ qf a)
    (sourceKPFixedFiniteCuspPeriod_ne_zero K hζ qf)

def sourceKPFixedFiniteCuspNonconstant (s : ℂ) (a : PGL(2,InfiniteAdeleRing K)) (x : Q) : ℂ :=
  sourceKPAutomorphicEisenstein K hζ s (sourceKPFixedFiniteCuspCover K hζ qf a x) -
    (sourceKPAdelicCompactScalar K hζ s (a,qf) + sourceKPAdelicTraceIntertwiner K hζ s (a,qf))

theorem sourceKPFixedFiniteCuspNonconstant_mk (s : ℂ) (a : PGL(2,InfiniteAdeleRing K)) (y : 𝔸[K]) :
    sourceKPFixedFiniteCuspNonconstant K hζ qf s a (QuotientAddGroup.mk y) =
      sourceKPAdelicNonconstantEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y * (a,qf)) := by
  change sourceKPAutomorphicEisenstein K hζ s
      (sourceKPAutomorphicLevelMk K hζ (sourceKPAdelicUpperLift K hζ y * (a,qf))) - _ = _
  rw [sourceKPAutomorphicEisenstein_mk,sourceKPAdelicNonconstantEisenstein_upper]

theorem sourceKPFixedFiniteCuspNonconstant_continuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (a : PGL(2,InfiniteAdeleRing K)) : Continuous (sourceKPFixedFiniteCuspNonconstant K hζ qf s a) := by
  apply (QuotientAddGroup.isQuotientMap_mk (sourceKPCuspPrincipalPeriods K D)).continuous_iff.mpr
  simpa only [Function.comp_def,sourceKPFixedFiniteCuspNonconstant_mk] using
    sourceKPAdelicNonconstantEisenstein_upper_continuous K hζ hs (a,qf)

def sourceKPFixedFiniteCuspNonconstantContinuous {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (a : PGL(2,InfiniteAdeleRing K)) : C(Q,ℂ) :=
  ⟨sourceKPFixedFiniteCuspNonconstant K hζ qf s a,
    sourceKPFixedFiniteCuspNonconstant_continuous K hζ qf hs a⟩

theorem sourceKPFixedFiniteCuspNonconstant_mean_zero {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (a : PGL(2,InfiniteAdeleRing K)) :
    (∫ x, sourceKPFixedFiniteCuspNonconstant K hζ qf s a x ∂sourceKPCuspTraceHaar K D) = 0 := by
  have hm := (sourceKPFixedFiniteCuspNonconstant_continuous K hζ qf hs a).aestronglyMeasurable
    (μ := sourceKPCuspTraceHaar K D)
  rw [sourceKPCuspTraceHaar,integral_map QuotientAddGroup.continuous_mk.measurable.aemeasurable hm]
  simpa only [sourceKPFixedFiniteCuspNonconstant_mk] using
    sourceKPAdelicNonconstantEisenstein_trace_mean_zero K hζ hs (a,qf)

def sourceKPFixedFiniteCuspNonconstantL2 {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (a : PGL(2,InfiniteAdeleRing K)) : SourceKPCuspL2 K D :=
  sourceKPCuspContinuousL2 K D hζ (sourceKPFixedFiniteCuspPeriod_ne_zero K hζ qf)
    (sourceKPFixedFiniteCuspNonconstantContinuous K hζ qf hs a)

theorem sourceKPFixedFiniteCuspNonconstantL2_mean_zero {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (a : PGL(2,InfiniteAdeleRing K)) :
    (∫ x, sourceKPFixedFiniteCuspNonconstantL2 K hζ qf hs a x ∂sourceKPCuspTraceHaar K D) = 0 :=
  (integral_congr_ae (sourceKPCuspContinuousL2_coe K D hζ
    (sourceKPFixedFiniteCuspPeriod_ne_zero K hζ qf)
    (sourceKPFixedFiniteCuspNonconstantContinuous K hζ qf hs a))).trans
      (sourceKPFixedFiniteCuspNonconstant_mean_zero K hζ qf hs a)

end
end ArtinMatthews
