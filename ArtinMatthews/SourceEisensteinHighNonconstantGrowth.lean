module

public import ArtinMatthews.SourceEisensteinHighRemainder
public import ArtinMatthews.SourceKPHeightBandReduction
public import ArtinMatthews.SourceEisensteinHighOutgoingBound
public import ArtinMatthews.SourceEisensteinRadialNonconstantGrowth
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

/-! A compact height-two representative and its actual radial return give
uniform polynomial growth of the genuine high-cusp nonconstant term. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Topology Set
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPHighCusp_compact_radialRepresentative (v₀ : InfinitePlace K)
    (T : ℝ) (hT : 2 ≤ T) (x : SourceKPHighCuspFinite K hζ T) :
    ∃ t : ℝ, 0 ≤ t ∧ ∃ (γ : sourceKPRationalBorel K) (q : SourceKPAdelicProjective K hζ)
      (g : GL (Fin 2) 𝔸[K]),
      g ∈ sourceKPHeightBandMatrices K hζ v₀ (Real.log 2) (Real.log 2) ∧
      sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g ∧
      sourceKPFiniteLevelRadialFlow K hζ t (sourceKPFiniteLevelMk K hζ q) = γ.val • x.val ∧
      sourceKPRadialHeightScale K t = sourceKPFiniteLevelHeight K hζ x.val / 2 := by
  let H := sourceKPFiniteLevelHeight K hζ x.val
  let c : ℝ := 2 * (Fintype.card (InfinitePlace K) : ℝ)
  let t := Real.log (H/2) / c
  have hc : 0 < c := mul_pos (by norm_num) (Nat.cast_pos.mpr Fintype.card_pos)
  have hH : 0 < H := sourceKPFiniteLevelHeight_pos K hζ x.val
  have hH2 : 2 ≤ H := hT.trans x.property.le
  have ht : 0 ≤ t := div_nonneg (Real.log_nonneg ((le_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
    (by simpa only [one_mul] using hH2))) hc.le
  have hct : c*t = Real.log (H/2) := by
    dsimp only [t]
    field_simp [hc.ne']
  have hscale : sourceKPRadialHeightScale K t = H/2 := by
    change Real.exp (c*t) = _
    rw [hct,Real.exp_log (div_pos hH (by norm_num))]
  let y := sourceKPFiniteLevelRadialFlow K hζ (-t) x.val
  have hy : sourceKPFiniteLevelHeight K hζ y = 2 := by
    change sourceKPFiniteLevelHeight K hζ (sourceKPFiniteLevelRadialFlow K hζ (-t) x.val) = _
    rw [sourceKPFiniteLevelRadialFlow_height]
    change sourceKPRadialHeightScale K (-t)*H = 2
    calc
      _ = 2*(sourceKPRadialHeightScale K (-t)*sourceKPRadialHeightScale K t) := by rw [hscale]; ring
      _ = _ := by rw [sourceKPRadialHeightScale_neg_mul,mul_one]
  obtain ⟨q,hq⟩ := sourceKPFiniteLevelMk_surjective K hζ y
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  have hg2 : sourceKPAdelicHeight K hζ g = 2 := by
    calc
      _ = sourceKPAdelicHeightOnProjective K hζ (ProjGenLinGroup.mk g) :=
        (sourceKPAdelicHeightOnProjective_mk K hζ g).symm
      _ = sourceKPAdelicCoverHeight K hζ q := congrArg (sourceKPAdelicHeightOnProjective K hζ) hg
      _ = sourceKPFiniteLevelHeight K hζ (sourceKPFiniteLevelMk K hζ q) :=
        (sourceKPFiniteLevelHeight_mk K hζ q).symm
      _ = _ := (congrArg (sourceKPFiniteLevelHeight K hζ) hq).trans hy
  obtain ⟨γ,g',hg',he⟩ := sourceKPHeightBand_matrix_reduction K hζ v₀ (Real.log 2) (Real.log 2) g
    (by rw [hg2]; exact ⟨le_rfl,le_rfl⟩)
  let q' := sourceKPAdelicProjectiveRationalLift K hζ γ*q
  have hq' : sourceKPAdelicProjectiveProjection K hζ q' = ProjGenLinGroup.mk g' := by
    dsimp only [q']
    rw [map_mul,sourceKPAdelicProjectiveRationalLift_projection,← hg]
    exact he
  have hγy : sourceKPFiniteLevelMk K hζ q' = γ • y :=
    (sourceKPFiniteLevelMk_rational K hζ γ q).trans (congrArg (γ • ·) hq)
  have hlog := sourceKPHeightBandMatrices_height K hζ v₀ (Real.log 2) (Real.log 2) g' hg'
  have hg'2 : sourceKPAdelicHeight K hζ g' = 2 := by
    have he := congrArg Real.exp (le_antisymm hlog.2 hlog.1)
    simpa only [Real.exp_log (sourceKPAdelicHeight_pos K hζ g'),Real.exp_log (by norm_num : (0 : ℝ)<2)] using he
  have hγH : sourceKPFiniteLevelHeight K hζ (γ • y) = 2 := by
    rw [← hγy,sourceKPFiniteLevelHeight_mk,sourceKPAdelicCoverHeight,hq',sourceKPAdelicHeightOnProjective_mk,hg'2]
  have hγB := sourceKPFiniteLevelHeight_high_overlap K hζ γ y
    (by rw [hy]; norm_num) (by rw [hγH]; norm_num)
  refine ⟨t,ht,⟨γ,hγB⟩,q',g',hg',hq',?_,hscale⟩
  rw [hγy,sourceKPFiniteLevelRadialFlow_rationalBorel K hζ t γ hγB]
  change γ • sourceKPFiniteLevelRadialFlow K hζ t
    (sourceKPFiniteLevelRadialFlow K hζ (-t) x.val) = γ • x.val
  rw [sourceKPFiniteLevelRadialFlow_add,add_neg_cancel,sourceKPFiniteLevelRadialFlow_zero]

theorem sourceKPHighCuspNonconstantEisenstein_growth {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (hT : 1 < T), 2 ≤ T →
      ∀ x : SourceKPHighCuspAutomorphic K hζ T,
        ‖sourceKPHighCuspNonconstantEisenstein K hζ s T hT x‖ ≤
          C*(sourceKPAutomorphicOrbitHeight K hζ x.val / 2)^(s.re+1/2) := by
  let v₀ : InfinitePlace K := Classical.choice inferInstance
  let S := sourceKPHeightBandMatrices K hζ v₀ (Real.log 2) (Real.log 2)
  have hS : IsCompact S := sourceKPHeightBandMatrices_isCompact K hζ v₀ _ _
  obtain ⟨C,hC,hbound⟩ := sourceKPAdelicNonconstantEisenstein_balanced_radial_growth K hζ hs S hS
  refine ⟨C,hC,?_⟩
  intro T hT hT2 x
  obtain ⟨a,rfl⟩ := sourceKPHighCuspQuotientMap_surjective K hζ T x
  induction a using Quotient.inductionOn with
  | _ y =>
    rw [sourceKPHighCuspQuotientMap_mk,sourceKPHighCuspNonconstantEisenstein_rep]
    obtain ⟨t,ht,γ,q,g,hg,hq,hflow,hscale⟩ := sourceKPHighCusp_compact_radialRepresentative K hζ v₀ T hT2 y
    have hR : sourceKPFiniteLevelNonconstantEisenstein K hζ s
        (sourceKPFiniteLevelRadialFlow K hζ t (sourceKPFiniteLevelMk K hζ q)) =
          sourceKPAdelicNonconstantEisenstein K hζ s (sourceKPArchRadialFlow K hζ t q.1,q.2) := by
      change sourceKPFiniteLevelNonconstantEisenstein K hζ s
        (sourceKPFiniteLevelMk K hζ (sourceKPArchRadialFlow K hζ t q.1,q.2)) = _
      exact sourceKPFiniteLevelNonconstantEisenstein_mk K hζ s _
    rw [← sourceKPFiniteLevelNonconstantEisenstein_rationalBorel K hζ s γ.val γ.property y.val,
      ← hflow,hR]
    change _ ≤ C*(sourceKPFiniteLevelOrbitHeight K hζ y.val / 2)^(s.re+1/2)
    rw [sourceKPFiniteLevelOrbitHeight_eq_height_of_high K hζ y.val (hT.trans y.property),← hscale]
    exact hbound g hg q hq t ht

end
end ArtinMatthews
