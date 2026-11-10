module

public import ArtinMatthews.SourceKPIdeleNormFlow
public import ArtinMatthews.SourceKPIdeleNormOneCompact
public import ArtinMatthews.SourceKPAdelicWeylCharacter
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

/-! Compact representatives for every bounded interval of logarithmic
idele norms, with the actual principal-idele action retained. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Topology
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPIdeleNormBand (v₀ : InfinitePlace K) (a b : ℝ) :
    Set (IdeleGroup (𝓞 K) K) :=
  (fun p : IdeleGroup (𝓞 K) K × ℝ => p.1 * sourceKPIdeleNormFlow K hζ v₀ p.2) ''
    (sourceKPIdeleNormOneCompact K ×ˢ Set.Icc a b)

theorem sourceKPIdeleNormBand_isCompact (v₀ : InfinitePlace K) (a b : ℝ) :
    IsCompact (sourceKPIdeleNormBand K hζ v₀ a b) :=
  ((sourceKPIdeleNormOneCompact_isCompact K).prod isCompact_Icc).image
    (continuous_fst.mul ((sourceKPIdeleNormFlow_continuous K hζ v₀).comp continuous_snd))

theorem sourceKPIdeleNormBand_log_norm (v₀ : InfinitePlace K) (a b : ℝ)
    (x : IdeleGroup (𝓞 K) K) (hx : x ∈ sourceKPIdeleNormBand K hζ v₀ a b) :
    Real.log (sourceKPIdeleAbsoluteNorm K x) ∈ Set.Icc a b := by
  obtain ⟨⟨c,t⟩,⟨hc,ht⟩,rfl⟩ := hx
  rw [map_mul, sourceKPIdeleNormOneCompact_norm K c hc,
    sourceKPIdeleNormFlow_norm, one_mul, Real.log_exp]
  exact ht

theorem sourceKPIdeleNormBand_representative (v₀ : InfinitePlace K) (a b : ℝ)
    (x : IdeleGroup (𝓞 K) K)
    (hx : Real.log (sourceKPIdeleAbsoluteNorm K x) ∈ Set.Icc a b) :
    ∃ q : Kˣ, x * IdeleGroup.unitEmbedding (𝓞 K) K q ∈ sourceKPIdeleNormBand K hζ v₀ a b := by
  let t := Real.log (sourceKPIdeleAbsoluteNorm K x)
  let c := x / sourceKPIdeleNormFlow K hζ v₀ t
  have hc : sourceKPIdeleAbsoluteNorm K c = 1 := by
    change sourceKPIdeleAbsoluteNorm K (x * (sourceKPIdeleNormFlow K hζ v₀ t)⁻¹) = 1
    rw [map_mul, sourceKPIdeleAbsoluteNorm_inv, sourceKPIdeleNormFlow_norm,
      Real.exp_log (sourceKPIdeleAbsoluteNorm_pos K x)]
    exact mul_inv_cancel₀ (sourceKPIdeleAbsoluteNorm_pos K x).ne'
  obtain ⟨q,hq⟩ := sourceKPIdeleNormOneCompact_representative K c hc
  refine ⟨q, ⟨(c * IdeleGroup.unitEmbedding (𝓞 K) K q,t), ⟨hq,hx⟩, ?_⟩⟩
  change (c * IdeleGroup.unitEmbedding (𝓞 K) K q) * sourceKPIdeleNormFlow K hζ v₀ t = _
  calc
    _ = (c * sourceKPIdeleNormFlow K hζ v₀ t) * IdeleGroup.unitEmbedding (𝓞 K) K q := by
      ac_rfl
    _ = _ := by rw [show c * sourceKPIdeleNormFlow K hζ v₀ t = x from div_mul_cancel x _]

include hζ in
theorem sourceKPIdeleNormBand_compact_representatives (v₀ : InfinitePlace K) (a b : ℝ) :
    ∃ C : Set (IdeleGroup (𝓞 K) K), IsCompact C ∧
      (∀ x ∈ C, Real.log (sourceKPIdeleAbsoluteNorm K x) ∈ Set.Icc a b) ∧
      ∀ x : IdeleGroup (𝓞 K) K, Real.log (sourceKPIdeleAbsoluteNorm K x) ∈ Set.Icc a b →
        ∃ q : Kˣ, x * IdeleGroup.unitEmbedding (𝓞 K) K q ∈ C :=
  ⟨sourceKPIdeleNormBand K hζ v₀ a b, sourceKPIdeleNormBand_isCompact K hζ v₀ a b,
    sourceKPIdeleNormBand_log_norm K hζ v₀ a b,
    sourceKPIdeleNormBand_representative K hζ v₀ a b⟩

end
end ArtinMatthews
