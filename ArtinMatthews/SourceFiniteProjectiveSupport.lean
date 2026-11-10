module

public import ArtinMatthews.SourceFiniteKP2CompactSection
public import ArtinMatthews.SourceKPFiniteAdeleProjective
public import ArtinMatthews.StandardAdelicLocalNontrivial
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace ArtinMatthews

open NumberField IsDedekindDomain Filter
open scoped NumberField AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPFiniteProjective_finite_support
    (g : SourceKPFiniteAdeleProjective K hζ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (a : SourceKPFiniteAdeleCover K hζ) (S : Finset (HeightOneSpectrum (𝓞 K))),
      sourceKPFiniteAdeleProjectiveMk K hζ a = g ∧ S₀ ⊆ S ∧
      StandardAdelic.traceBadPlaces K ⊆ S ∧
      ∀ P ∉ S, (6 : 𝓞 K) ∉ P.asIdeal ∧
        SourceKPIntegralMatrix (sourceKPFiniteVal K P) (sourceKPAdeleMatrixAt K P a.base) := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (sourceKPFiniteAdeleScalar K hζ).range g
  have hgood : ∀ᶠ P : HeightOneSpectrum (𝓞 K) in cofinite,
      P ∉ S₀ ∧ P ∉ StandardAdelic.traceBadPlaces K ∧ (6 : 𝓞 K) ∉ P.asIdeal ∧
        SourceKPIntegralMatrix (sourceKPFiniteVal K P) (sourceKPAdeleMatrixAt K P a.base) := by
    filter_upwards [S₀.eventually_cofinite_notMem,
      (StandardAdelic.traceBadPlaces K).eventually_cofinite_notMem,
      sourceKPAdele_eventually_tame K, sourceKPAdeleMatrixAt_eventually_integral K a.base] with P h₀ hbad h₆ hInt
    exact ⟨h₀, hbad, h₆, hInt⟩
  have hfinite := Filter.eventually_cofinite.mp hgood
  refine ⟨a, hfinite.toFinset, ha, ?_, ?_, ?_⟩
  · intro P hP
    apply hfinite.mem_toFinset.mpr
    intro h
    exact h.1 hP
  · intro P hP
    apply hfinite.mem_toFinset.mpr
    intro h
    exact h.2.1 hP
  · intro P hP
    have h : ¬¬(P ∉ S₀ ∧ P ∉ StandardAdelic.traceBadPlaces K ∧ (6 : 𝓞 K) ∉ P.asIdeal ∧
        SourceKPIntegralMatrix (sourceKPFiniteVal K P) (sourceKPAdeleMatrixAt K P a.base)) := by
      intro hn
      exact hP (hfinite.mem_toFinset.mpr hn)
    exact (Classical.not_not.mp h).2.2

theorem sourceKPFiniteProjective_support_compact
    (g : SourceKPFiniteAdeleProjective K hζ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (a : SourceKPFiniteAdeleCover K hζ) (S : Finset (HeightOneSpectrum (𝓞 K))),
      sourceKPFiniteAdeleProjectiveMk K hζ a = g ∧ S₀ ⊆ S ∧
      StandardAdelic.traceBadPlaces K ⊆ S ∧
      ∀ P ∉ S, (6 : 𝓞 K) ∉ P.asIdeal ∧
        ∃ k : SourceFiniteKP2Integral K P, k.val = sourceKPAdeleMatrixAt K P a.base := by
  obtain ⟨a, S, ha, hS₀, hbad, hInt⟩ := sourceKPFiniteProjective_finite_support K hζ g S₀
  refine ⟨a, S, ha, hS₀, hbad, ?_⟩
  intro P hP
  exact ⟨(hInt P hP).1, ⟨⟨sourceKPAdeleMatrixAt K P a.base, (hInt P hP).2⟩, rfl⟩⟩

end
end ArtinMatthews
