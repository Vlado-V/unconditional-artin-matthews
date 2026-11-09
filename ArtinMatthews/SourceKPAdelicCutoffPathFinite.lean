module

public import ArtinMatthews.SourceKPAdelicUpperChartTopology
public import ArtinMatthews.SourceKPAdelicCuspCutoff


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
