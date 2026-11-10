module

public import ArtinMatthews.SourceKPAdelicRationalProductChart
public import ArtinMatthews.SourceKPAdelicProductChartTopology
public import ArtinMatthews.SourceKPAdelicRationalCompactBound
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

/-! A single summable bound for every rational summand on a compact
subset of the actual product chart. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix OAI.CubicEisenstein SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicRationalProductChart_compact_bound {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) (S : Set (InfinitePlace K → EuclideanSpatial))
    (hS : IsCompact S) (hpos : ∀ p ∈ S, ∀ v, 0 < p v 2) :
    ∃ M : SourceKPRationalBorelCoset K → ℝ, Summable M ∧
      ∀ c p, p ∈ S → ‖sourceKPAdelicRationalProductChart K hζ s q c p‖ ≤ M c := by
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let σ : S → SourceKPProductUpper K := fun p => ⟨p.val,hpos p.val p.property⟩
  have hσ : Continuous σ := continuous_subtype_val.subtype_mk _
  let A : S → GL (Fin 2) 𝔸[K] := fun p => sourceKPAdelicProductUpperMatrix K hζ g (σ p)
  have hA : Continuous A := (sourceKPAdelicProductUpperMatrix_continuous K hζ g).comp hσ
  obtain ⟨M,hM,hbound⟩ := sourceKPAdelicRationalSummand_compact_bound K hζ hs
    (Set.range A) (isCompact_range hA)
  refine ⟨M,hM,?_⟩
  intro c p hp
  let p₀ : S := ⟨p,hp⟩
  have hb := hbound (A p₀) (Set.mem_range_self p₀)
    (q*(ProjGenLinGroup.mk (sourceKPProductUpperSection K hζ (σ p₀)),1))
    (sourceKPAdelicProductUpperMatrix_projection K hζ q g hg.symm (σ p₀)) c
  change ‖(if h : ∀ v, 0 < p v 2 then _ else (0 : ℂ))‖ ≤ M c
  rw [dite_eq_left (hpos p hp)]
  simpa only [σ,p₀,sourceKPProductUpperSection_eq] using hb

end
end ArtinMatthews
