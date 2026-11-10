module

public import ArtinMatthews.SourceKPAdelicCuspCutoff
public import ArtinMatthews.SourceArchSingleRightAction
public import ArtinMatthews.SourceKPAdelicUpperChartTopology
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

/-! Uniform finite rational support near every actual archimedean
matrix path, with no restriction on the spectral parameter. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Filter
open SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups BigOperators Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCutoff_path_finite_near {T : ℝ} (hT : 0 < T)
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K)
    (γ : ℝ → GL (Fin 2) ℂ) (hγ : Continuous γ) :
    ∃ I : Finset (SourceKPRationalBorelCoset K), ∀ s : ℂ,
      ((fun t => sourceKPAdelicCutoffEisenstein K hζ T s
        (q*sourceArchGroupSingle K hζ v (γ t))) =ᶠ[𝓝 0]
          (fun t => ∑ c ∈ I, sourceKPAdelicRationalSummand K hζ
            (sourceKPAdelicCutoffSeed K hζ T s) (q*sourceArchGroupSingle K hζ v (γ t)) c)) ∧
      ∀ c ∉ I, ((fun t => sourceKPAdelicRationalSummand K hζ
        (sourceKPAdelicCutoffSeed K hζ T s) (q*sourceArchGroupSingle K hζ v (γ t)) c) =ᶠ[𝓝 0]
          fun _ => 0) := by
  classical
  let C := Set.Icc (-1 : ℝ) 1
  let : CompactSpace C := isCompact_iff_compactSpace.mp isCompact_Icc
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  let A : C → GL (Fin 2) 𝔸[K] :=
    fun t => g*sourceKPAdelicArchSingleMatrix K hζ v (γ t.val)
  have hA : Continuous A := continuous_const.mul
    ((sourceKPAdelicArchSingleMatrix_continuous K hζ v).comp (hγ.comp continuous_subtype_val))
  obtain ⟨I,hI,hzero⟩ := sourceKPAdelicCutoffSummand_uniform_finite K hζ hT
    (Set.range A) (isCompact_range hA)
  have hC : C ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hz (s : ℂ) (c : SourceKPRationalBorelCoset K) (hc : c ∉ hI.toFinset)
      (t : ℝ) (ht : t ∈ C) :
      sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s)
        (q*sourceArchGroupSingle K hζ v (γ t)) c = 0 := by
    let t₀ : C := ⟨t,ht⟩
    apply hzero s (A t₀) (Set.mem_range_self t₀)
      (q*sourceArchGroupSingle K hζ v (γ t)) _ c
      (by simpa only [Set.Finite.mem_toFinset] using hc)
    rw [map_mul,← hg,sourceKPAdelicArchSingleMatrix_projection,← map_mul]
  refine ⟨hI.toFinset,fun s => ⟨?_,?_⟩⟩
  · filter_upwards [hC] with t ht
    change (∑' c, sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s)
      (q*sourceArchGroupSingle K hζ v (γ t)) c) = _
    exact tsum_eq_sum (fun c hc => hz s c hc t ht)
  · intro c hc
    filter_upwards [hC] with t ht
    exact hz s c hc t ht

end
end ArtinMatthews
