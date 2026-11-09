module

public import ArtinMatthews.SourceKPIdeleNormFlow
public import ArtinMatthews.SourceKPIdeleNormOneCompact


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
