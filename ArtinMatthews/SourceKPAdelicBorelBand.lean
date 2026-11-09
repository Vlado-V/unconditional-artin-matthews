module

public import ArtinMatthews.SourceKPIdeleNormBand
public import ArtinMatthews.SourceKPAdelicUpperTopology
public import ArtinMatthews.SourceKPAdelicSectionBound
public import ArtinMatthews.SourceAdelicFundamentalDomain


set_option backward.privateInPublic true
@[expose] public section

/-! Compact bounded-height Borel representatives modulo the actual
rational Borel action. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Topology
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicDiagonalMatrix_continuous : Continuous (sourceKPDiagonalHom 𝔸[K]) := by
  apply Continuous.of_coeHom_comp
  change Continuous (fun a : IdeleGroup (𝓞 K) K =>
    (sourceKPDiagonalHom 𝔸[K] a : Matrix (Fin 2) (Fin 2) 𝔸[K]))
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j
  · exact Units.continuous_val
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

def sourceKPAdelicBorelBand (v₀ : InfinitePlace K) (a b : ℝ) :
    Set (GL (Fin 2) 𝔸[K]) :=
  (fun p : 𝔸[K] × IdeleGroup (𝓞 K) K =>
    sourceKPUpperMatrix 𝔸[K] p.1 * sourceKPDiagonalHom 𝔸[K] p.2) ''
      (CompactQuotient.Construction.adelicCompactRepresentatives K ×ˢ
        sourceKPIdeleNormBand K hζ v₀ a b)

theorem sourceKPAdelicBorelBand_isCompact (v₀ : InfinitePlace K) (a b : ℝ) :
    IsCompact (sourceKPAdelicBorelBand K hζ v₀ a b) :=
  ((CompactQuotient.Construction.isCompact_adelicCompactRepresentatives K).prod
    (sourceKPIdeleNormBand_isCompact K hζ v₀ a b)).image
      (((sourceKPAdelicUpperMatrix_continuous K).comp continuous_fst).mul
        ((sourceKPAdelicDiagonalMatrix_continuous K).comp continuous_snd))

theorem sourceKPAdelicHeight_upper_diagonal (x : 𝔸[K]) (u : IdeleGroup (𝓞 K) K) :
    sourceKPAdelicHeight K hζ (sourceKPUpperMatrix 𝔸[K] x * sourceKPDiagonalHom 𝔸[K] u) =
      sourceKPIdeleAbsoluteNorm K u := by
  have hb := (sourceKPRingNormalizedBorel 𝔸[K]).mul_mem
    (sourceKPRingNormalizedBorel_upper 𝔸[K] x) (sourceKPRingNormalizedBorel_diagonal 𝔸[K] u)
  rw [sourceKPAdelicHeight_factor K hζ _ _ 1 1 hb
    (SourceKPAdelicBaseCompactMatrix K hζ).one_mem (by simp), sourceKPUpperDiagonal_det]

theorem sourceKPAdelicBorelBand_height (v₀ : InfinitePlace K) (a b : ℝ)
    (g : GL (Fin 2) 𝔸[K]) (hg : g ∈ sourceKPAdelicBorelBand K hζ v₀ a b) :
    Real.log (sourceKPAdelicHeight K hζ g) ∈ Set.Icc a b := by
  obtain ⟨⟨x,u⟩,⟨_,hu⟩,rfl⟩ := hg
  rw [sourceKPAdelicHeight_upper_diagonal]
  exact sourceKPIdeleNormBand_log_norm K hζ v₀ a b u hu

theorem sourceKPAdelicBorelBand_reduce (v₀ : InfinitePlace K) (a b : ℝ)
    (x : 𝔸[K]) (u : IdeleGroup (𝓞 K) K)
    (hu : Real.log (sourceKPIdeleAbsoluteNorm K u) ∈ Set.Icc a b) :
    ∃ (q : Kˣ) (r : K),
      GeneralLinearGroup.map (algebraMap K 𝔸[K])
        (sourceKPUpperMatrix K r * sourceKPDiagonalHom K q) *
          (sourceKPUpperMatrix 𝔸[K] x * sourceKPDiagonalHom 𝔸[K] u) ∈
            sourceKPAdelicBorelBand K hζ v₀ a b := by
  obtain ⟨q,hq⟩ := sourceKPIdeleNormBand_representative K hζ v₀ a b u hu
  let p := IdeleGroup.unitEmbedding (𝓞 K) K q
  obtain ⟨r,hr⟩ := sourceKPAdelicFundamentalDomain_exists K ((p : 𝔸[K])*x)
  refine ⟨q,-r, ?_⟩
  have he : GeneralLinearGroup.map (algebraMap K 𝔸[K])
      (sourceKPUpperMatrix K (-r) * sourceKPDiagonalHom K q) *
        (sourceKPUpperMatrix 𝔸[K] x * sourceKPDiagonalHom 𝔸[K] u) =
      sourceKPUpperMatrix 𝔸[K] ((p : 𝔸[K])*x-algebraMap K 𝔸[K] r) *
        sourceKPDiagonalHom 𝔸[K] (u*p) := by
    rw [map_mul, sourceKPUpperMatrix_map, sourceKPDiagonalHom_map, map_neg]
    change sourceKPUpperMatrix 𝔸[K] (-algebraMap K 𝔸[K] r) * sourceKPDiagonalHom 𝔸[K] p *
      (sourceKPUpperMatrix 𝔸[K] x * sourceKPDiagonalHom 𝔸[K] u) = _
    calc
      _ = sourceKPUpperMatrix 𝔸[K] (-algebraMap K 𝔸[K] r) *
          (sourceKPDiagonalHom 𝔸[K] p * sourceKPUpperMatrix 𝔸[K] x) *
            sourceKPDiagonalHom 𝔸[K] u := by group
      _ = sourceKPUpperMatrix 𝔸[K] (-algebraMap K 𝔸[K] r) *
          (sourceKPUpperMatrix 𝔸[K] ((p : 𝔸[K])*x) * sourceKPDiagonalHom 𝔸[K] p) *
            sourceKPDiagonalHom 𝔸[K] u := by rw [sourceKPDiagonalHom_upper]
      _ = sourceKPUpperMatrix 𝔸[K] (-algebraMap K 𝔸[K] r+(p : 𝔸[K])*x) *
          sourceKPDiagonalHom 𝔸[K] (p*u) := by
        rw [sourceKPUpperMatrix_add, map_mul]
        group
      _ = _ := by rw [neg_add_eq_sub, mul_comm p u]
  rw [he]
  exact ⟨(((p : 𝔸[K])*x-algebraMap K 𝔸[K] r),u*p),
    ⟨sourceKPAdelicFundamentalDomain_subset_compact K hr,hq⟩,rfl⟩

end
end ArtinMatthews
