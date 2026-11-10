module

public import ArtinMatthews.SourceKPHighCuspQuotient
public import ArtinMatthews.SourceKPHeightBandReduction
public import ArtinMatthews.SourceKPAdelicHeightAction
public import ArtinMatthews.SourceKPArchRadialFlow
public import ArtinMatthews.SourceKPHeightBandCompact
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! One fixed finite set of finite-level fibers represents the whole high
cusp. Radial normalization reduces the arithmetic selection to height two. -/
namespace ArtinMatthews
open NumberField Matrix Topology Set
open scoped NumberField MatrixGroups AdeleRing Pointwise

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPCuspFixedFiniteFibers (v₀ : InfinitePlace K) :
    Set (SourceKPFiniteLevelFiber K hζ) :=
  sourceKPCompactFiniteFibers K hζ (sourceKPHeightBandMatrices K hζ v₀ (Real.log 2) (Real.log 2))

theorem sourceKPCuspFixedFiniteFibers_finite (v₀ : InfinitePlace K) :
    (sourceKPCuspFixedFiniteFibers K hζ v₀).Finite :=
  sourceKPCompactFiniteFibers_finite K hζ _
    (sourceKPHeightBandMatrices_isCompact K hζ v₀ (Real.log 2) (Real.log 2))

private theorem sourceKPCuspHeightBand_log (v₀ : InfinitePlace K) (a b : ℝ)
    (g : GL (Fin 2) 𝔸[K]) (hg : g ∈ sourceKPHeightBandMatrices K hζ v₀ a b) :
    Real.log (sourceKPAdelicHeight K hζ g) ∈ Set.Icc a b := by
  obtain ⟨v,hv,k,hk,rfl⟩ := Set.mem_mul.mp hg
  rw [sourceKPAdelicHeight_right_baseCompact K hζ v k hk]
  exact sourceKPAdelicBorelBand_height K hζ v₀ a b v hv

private theorem sourceKPCuspRadialHeightTwo (x : SourceKPFiniteLevelSpace K hζ) :
    ∃ t : ℝ, sourceKPFiniteLevelHeight K hζ (sourceKPFiniteLevelRadialFlow K hζ t x) = 2 := by
  let H := sourceKPFiniteLevelHeight K hζ x
  let c : ℝ := 2 * (Fintype.card (InfinitePlace K) : ℝ)
  let t := Real.log (2/H) / c
  have hH : 0 < H := sourceKPFiniteLevelHeight_pos K hζ x
  have hc : 0 < c := mul_pos (by norm_num) (Nat.cast_pos.mpr Fintype.card_pos)
  refine ⟨t,?_⟩
  rw [sourceKPFiniteLevelRadialFlow_height]
  change Real.exp (c*t)*H = 2
  have ht : c*t = Real.log (2/H) := by
    dsimp only [t]
    field_simp [hc.ne']
  rw [ht,Real.exp_log (div_pos (by norm_num) hH),div_mul_cancel₀ _ hH.ne']

theorem sourceKPCuspFixedFiniteFibers_representative (v₀ : InfinitePlace K)
    (T : ℝ) (x : SourceKPHighCuspFinite K hζ T) :
    ∃ γ : sourceKPRationalBorel K, (γ • x).val.2 ∈ sourceKPCuspFixedFiniteFibers K hζ v₀ := by
  obtain ⟨t,ht⟩ := sourceKPCuspRadialHeightTwo K hζ x.val
  let y := sourceKPFiniteLevelRadialFlow K hζ t x.val
  obtain ⟨q,hq⟩ := sourceKPFiniteLevelMk_surjective K hζ y
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  have hg2 : sourceKPAdelicHeight K hζ g = 2 := by
    calc
      _ = sourceKPAdelicHeightOnProjective K hζ (ProjGenLinGroup.mk g) :=
        (sourceKPAdelicHeightOnProjective_mk K hζ g).symm
      _ = sourceKPAdelicCoverHeight K hζ q :=
        congrArg (sourceKPAdelicHeightOnProjective K hζ) hg
      _ = sourceKPFiniteLevelHeight K hζ (sourceKPFiniteLevelMk K hζ q) :=
        (sourceKPFiniteLevelHeight_mk K hζ q).symm
      _ = _ := (congrArg (sourceKPFiniteLevelHeight K hζ) hq).trans ht
  obtain ⟨γ,g',hg',he⟩ := sourceKPHeightBand_matrix_reduction K hζ v₀ (Real.log 2) (Real.log 2) g
    (by rw [hg2]; exact ⟨le_rfl,le_rfl⟩)
  let q' := sourceKPAdelicProjectiveRationalLift K hζ γ*q
  have hq' : sourceKPAdelicProjectiveProjection K hζ q' = ProjGenLinGroup.mk g' := by
    dsimp only [q']
    rw [map_mul, sourceKPAdelicProjectiveRationalLift_projection, ← hg]
    exact he
  have hγy : sourceKPFiniteLevelMk K hζ q' = γ • y :=
    (sourceKPFiniteLevelMk_rational K hζ γ q).trans (congrArg (γ • ·) hq)
  have hlog := sourceKPCuspHeightBand_log K hζ v₀ (Real.log 2) (Real.log 2) g' hg'
  have hg'2 : sourceKPAdelicHeight K hζ g' = 2 := by
    have h := congrArg Real.exp (le_antisymm hlog.2 hlog.1)
    simpa only [Real.exp_log (sourceKPAdelicHeight_pos K hζ g'), Real.exp_log (by norm_num : (0:ℝ)<2)]
      using h
  have hγH : sourceKPFiniteLevelHeight K hζ (γ • y) = 2 := by
    calc
      _ = sourceKPFiniteLevelHeight K hζ (sourceKPFiniteLevelMk K hζ q') :=
        congrArg (sourceKPFiniteLevelHeight K hζ) hγy.symm
      _ = sourceKPAdelicCoverHeight K hζ q' := sourceKPFiniteLevelHeight_mk K hζ q'
      _ = sourceKPAdelicHeightOnProjective K hζ (ProjGenLinGroup.mk g') :=
        congrArg (sourceKPAdelicHeightOnProjective K hζ) hq'
      _ = _ := (sourceKPAdelicHeightOnProjective_mk K hζ g').trans hg'2
  have hγB := sourceKPFiniteLevelHeight_high_overlap K hζ γ y
    (by rw [ht]; norm_num) (by rw [hγH]; norm_num)
  have hm := sourceKPCompactLevelContainer_mem K hζ _ q' g' hg' hq'
  refine ⟨⟨γ,hγB⟩,?_⟩
  have hf := congrArg Prod.snd hγy
  change (sourceKPFiniteLevelMk K hζ q').2 = (γ • x.val).2 at hf
  exact hf ▸ hm.2

end
end ArtinMatthews
