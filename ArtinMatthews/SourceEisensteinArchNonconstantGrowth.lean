module

public import ArtinMatthews.SourceEisensteinNonconstant
public import ArtinMatthews.SourceArchOnlyIdele
public import ArtinMatthews.SourceEisensteinArchDiagonalGrowth
public import ArtinMatthews.SourceKPAdelicUpperProjection
public import ArtinMatthews.SourceKPAdelicUpperTopology
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

/-! The actual zero-mean remainder has uniform growth along all expanding archimedean diagonals. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceArchNonconstantAdelicMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceArchNonconstantAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩

theorem sourceKPAdelicNonconstantEisenstein_archDiagonal_growth {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (S : Set (GL (Fin 2) 𝔸[K])) (hS : IsCompact S) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ S, ∀ a : (InfiniteAdeleRing K)ˣ,
      (∀ v, 1 ≤ ‖(a : InfiniteAdeleRing K) v‖) → ∀ q : SourceKPAdelicProjective K hζ,
      sourceKPAdelicProjectiveProjection K hζ q =
          ProjGenLinGroup.mk (g * sourceKPDiagonalHom 𝔸[K] (sourceArchOnlyIdele K a)) →
      ‖sourceKPAdelicNonconstantEisenstein K hζ s q‖ ≤ C * ‖(a : InfiniteAdeleRing K)‖ ^ (s.re + 1 / 2) := by
  let A := (fun p : 𝔸[K] × GL (Fin 2) 𝔸[K] => sourceKPUpperMatrix 𝔸[K] p.1 * p.2) ''
    (CompactQuotient.Construction.adelicCompactRepresentatives K ×ˢ S)
  have hA : IsCompact A :=
    ((CompactQuotient.Construction.isCompact_adelicCompactRepresentatives K).prod hS).image
      (((sourceKPAdelicUpperMatrix_continuous K).comp continuous_fst).mul continuous_snd)
  obtain ⟨C, hC, hbound⟩ := sourceKPAdelicCompactEisenstein_archDiagonal_growth K hζ hs
    (S ∪ A) (hS.union hA)
  refine ⟨2 * C, by positivity, ?_⟩
  intro g hg a ha q hq
  have hE := hbound g (Or.inl hg) a ha q hq
  let μ := sourceKPAdelicTraceProduct K
  let D := sourceKPAdelicFundamentalDomain K
  have hD : μ D = 1 := sourceKPAdelicTraceProduct_fundamentalDomain_of_primitiveRoot K hζ
  let : IsProbabilityMeasure (μ.restrict D) := ⟨by rw [Measure.restrict_apply_univ, hD]⟩
  have hEN : ∀ᵐ y ∂μ.restrict D,
      ‖sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y * q)‖ ≤
        C * ‖(a : InfiniteAdeleRing K)‖ ^ (s.re + 1 / 2) := by
    filter_upwards [ae_restrict_mem (sourceKPAdelicFundamentalDomain_measurable K)] with y hy
    have hgy : sourceKPUpperMatrix 𝔸[K] y * g ∈ A :=
      ⟨(y, g), ⟨sourceKPAdelicFundamentalDomain_subset_compact K hy, hg⟩, rfl⟩
    apply hbound _ (Or.inr hgy) a ha (sourceKPAdelicUpperLift K hζ y * q)
    rw [map_mul, sourceKPAdelicUpperLift_projection, hq, ← map_mul, mul_assoc]
  have hmean : ‖∫ y in D,
      sourceKPAdelicCompactEisenstein K hζ s (sourceKPAdelicUpperLift K hζ y * q) ∂μ‖ ≤
        C * ‖(a : InfiniteAdeleRing K)‖ ^ (s.re + 1 / 2) := by
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const hEN
  rw [sourceKPAdelicNonconstantEisenstein,
    ← sourceKPAdelicCompactEisenstein_traceConstantTerm K hζ hs q]
  exact (norm_sub_le _ _).trans (by linarith)

end
end ArtinMatthews
