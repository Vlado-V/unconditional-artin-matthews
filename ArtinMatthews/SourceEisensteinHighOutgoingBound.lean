module

public import ArtinMatthews.SourceEisensteinHighOutgoing
public import ArtinMatthews.SourceKPHeightBandCompact


set_option backward.privateInPublic true
@[expose] public section

/-! Actual outgoing terms are bounded on each finite high-height band, using
compact Borel representatives and the genuine high-cusp separation theorem. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPHeightBandMatrices_height (v₀ : InfinitePlace K) (a b : ℝ)
    (g : GL (Fin 2) 𝔸[K]) (hg : g ∈ sourceKPHeightBandMatrices K hζ v₀ a b) :
    Real.log (sourceKPAdelicHeight K hζ g) ∈ Set.Icc a b := by
  obtain ⟨v,hv,k,hk,rfl⟩ := hg
  rw [sourceKPAdelicHeight_right_baseCompact K hζ v k hk]
  exact sourceKPAdelicBorelBand_height K hζ v₀ a b v hv

theorem sourceKPAdelicTraceIntertwiner_heightBand_bound {s : ℂ} (hs : 0 < s.re)
    (T U : ℝ) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : SourceKPAdelicProjective K hζ,
      T < sourceKPAdelicCoverHeight K hζ q → sourceKPAdelicCoverHeight K hζ q ≤ U →
        ‖sourceKPAdelicTraceIntertwiner K hζ s q‖ ≤ C := by
  let v₀ : InfinitePlace K := Classical.choice inferInstance
  let S := sourceKPHeightBandMatrices K hζ v₀ (Real.log T) (Real.log U)
  have hS : IsCompact S := sourceKPHeightBandMatrices_isCompact K hζ v₀ _ _
  have hcompact := sourceKPCompactLevelContainer_isCompact K hζ S hS
  obtain ⟨B,hB⟩ := hcompact.bddAbove_image
    (sourceKPFiniteLevelOutgoingEisenstein_continuous K hζ hs).norm.continuousOn
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro q hqT hqU
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  have hh : sourceKPAdelicHeight K hζ g = sourceKPAdelicCoverHeight K hζ q := by
    unfold sourceKPAdelicCoverHeight
    rw [← hg,sourceKPAdelicHeightOnProjective_mk]
  have hband : Real.log (sourceKPAdelicHeight K hζ g) ∈ Set.Icc (Real.log T) (Real.log U) := by
    rw [hh]
    exact ⟨Real.log_le_log (zero_lt_one.trans hT) hqT.le,
      Real.log_le_log (sourceKPAdelicCoverHeight_pos K hζ q) hqU⟩
  obtain ⟨γ,g',hg',he⟩ := sourceKPHeightBand_matrix_reduction K hζ v₀ _ _ g hband
  let q' := sourceKPAdelicProjectiveRationalLift K hζ γ * q
  have hq' : sourceKPAdelicProjectiveProjection K hζ q' = ProjGenLinGroup.mk g' := by
    dsimp only [q']
    rw [map_mul,sourceKPAdelicProjectiveRationalLift_projection,← hg]
    exact he
  have hh' : sourceKPAdelicCoverHeight K hζ q' = sourceKPAdelicHeight K hζ g' := by
    rw [sourceKPAdelicCoverHeight,hq',sourceKPAdelicHeightOnProjective_mk]
  have hlow := (sourceKPHeightBandMatrices_height K hζ v₀ (Real.log T) (Real.log U) g' hg').1
  have hTg : T ≤ sourceKPAdelicHeight K hζ g' :=
    (Real.log_le_log_iff (zero_lt_one.trans hT) (sourceKPAdelicHeight_pos K hζ g')).mp hlow
  have hγ : γ ∈ sourceKPRationalBorel K :=
    sourceKPAdelicCoverHeight_high_overlap K hζ q γ (hT.trans hqT)
      (by change 1 < sourceKPAdelicCoverHeight K hζ q'; rw [hh']; exact hT.trans_le hTg)
  have hmem := sourceKPCompactLevelContainer_mem K hζ S q' g' hg' hq'
  have hbound : ‖sourceKPFiniteLevelOutgoingEisenstein K hζ s (sourceKPFiniteLevelMk K hζ q')‖ ≤ B :=
    hB ⟨sourceKPFiniteLevelMk K hζ q',hmem,rfl⟩
  rw [sourceKPFiniteLevelOutgoingEisenstein_mk] at hbound
  dsimp only [q'] at hbound
  rw [sourceKPAdelicTraceIntertwiner_rationalBorel K hζ s γ hγ] at hbound
  exact hbound.trans (le_max_right _ _)

theorem sourceKPHighCuspOutgoingEisenstein_band_bound {s : ℂ} (hs : 0 < s.re)
    (T U : ℝ) (hT : 1 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : SourceKPHighCuspAutomorphic K hζ T,
      sourceKPAutomorphicOrbitHeight K hζ x.val ≤ U →
        ‖sourceKPHighCuspOutgoingEisenstein K hζ s T hT x‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := sourceKPAdelicTraceIntertwiner_heightBand_bound K hζ hs T U hT
  refine ⟨C,hC,?_⟩
  intro x hx
  obtain ⟨a,rfl⟩ := sourceKPHighCuspQuotientMap_surjective K hζ T x
  induction a using Quotient.inductionOn with
  | _ y =>
    rw [sourceKPHighCuspQuotientMap_mk,sourceKPHighCuspOutgoingEisenstein_rep]
    obtain ⟨q,hq⟩ := sourceKPFiniteLevelMk_surjective K hζ y.val
    rw [← hq,sourceKPFiniteLevelOutgoingEisenstein_mk]
    apply hbound q
    · have h := y.property
      rw [← hq,sourceKPFiniteLevelHeight_mk] at h
      exact h
    · change sourceKPFiniteLevelOrbitHeight K hζ y.val ≤ U at hx
      rw [sourceKPFiniteLevelOrbitHeight_eq_height_of_high K hζ y.val (hT.trans y.property),
        ← hq,sourceKPFiniteLevelHeight_mk] at hx
      exact hx

end
end ArtinMatthews
