module

public import ArtinMatthews.SourceKPArchDoubleQuotient


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPFiniteLevelToCompact (x : SourceKPFiniteLevelSpace K hζ) :
    SourceKPAutomorphicCompactLevel K hζ :=
  sourceKPAutomorphicCompactMk K hζ (Quotient.mk _ x)

theorem sourceKPFiniteLevelToCompact_isOpenQuotientMap :
    IsOpenQuotientMap (sourceKPFiniteLevelToCompact K hζ) := by
  have ha : IsOpenQuotientMap
      (Quotient.mk _ : SourceKPFiniteLevelSpace K hζ → SourceKPAutomorphicLevel K hζ) :=
    MulAction.isOpenQuotientMap_quotientMk
  exact (sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).comp ha

theorem sourceKPAutomorphicCompactFamily_continuous_of_fibers
    (f : ℂ → SourceKPAutomorphicCompactLevel K hζ → ℂ)
    (hf : ∀ b : SourceKPFiniteLevelFiber K hζ,
      Continuous (fun p : ℂ × PGL(2, InfiniteAdeleRing K) =>
        f p.1 (sourceKPAutomorphicCompactMk K hζ (sourceKPArchComponentPoint K hζ b p.2)))) :
    Continuous (fun p : ℂ × SourceKPAutomorphicCompactLevel K hζ => f p.1 p.2) := by
  let g : (ℂ × PGL(2, InfiniteAdeleRing K)) × SourceKPFiniteLevelFiber K hζ → ℂ :=
    fun p => f p.1.1 (sourceKPFiniteLevelToCompact K hζ (p.1.2,p.2))
  have hg : Continuous g := continuous_prod_of_discrete_right.mpr hf
  have hr : Continuous
      (fun p : ℂ × SourceKPFiniteLevelSpace K hζ => ((p.1,p.2.1),p.2.2)) :=
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd)
  have hq : IsOpenQuotientMap
      (Prod.map (id : ℂ → ℂ) (sourceKPFiniteLevelToCompact K hζ)) :=
    IsOpenQuotientMap.id.prodMap (sourceKPFiniteLevelToCompact_isOpenQuotientMap K hζ)
  exact hq.continuous_comp_iff.mp (hg.comp hr)

theorem sourceKPAutomorphicCompactFamily_continuous_of_projective
    (f : ℂ → SourceKPAutomorphicCompactLevel K hζ → ℂ)
    (hf : ∀ qf : SourceKPFiniteAdeleProjective K hζ,
      Continuous (fun p : ℂ × PGL(2, InfiniteAdeleRing K) =>
        f p.1 (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ (p.2,qf))))) :
    Continuous (fun p : ℂ × SourceKPAutomorphicCompactLevel K hζ => f p.1 p.2) := by
  apply sourceKPAutomorphicCompactFamily_continuous_of_fibers K hζ f
  intro b
  obtain ⟨qf,rfl⟩ := Quotient.exists_rep b
  exact hf qf

theorem sourceKPArchProjectiveProjection_isOpenQuotientMap :
    IsOpenQuotientMap (ProjGenLinGroup.mk : GL (Fin 2) (InfiniteAdeleRing K) →
      PGL(2, InfiniteAdeleRing K)) :=
  QuotientGroup.isOpenQuotientMap_mk

theorem sourceKPAutomorphicCompactFamily_continuous_of_matrices
    (f : ℂ → SourceKPAutomorphicCompactLevel K hζ → ℂ)
    (hf : ∀ qf : SourceKPFiniteAdeleProjective K hζ,
      Continuous (fun p : ℂ × GL (Fin 2) (InfiniteAdeleRing K) =>
        f p.1 (sourceKPAutomorphicCompactMk K hζ
          (sourceKPAutomorphicLevelMk K hζ (ProjGenLinGroup.mk p.2,qf))))) :
    Continuous (fun p : ℂ × SourceKPAutomorphicCompactLevel K hζ => f p.1 p.2) := by
  apply sourceKPAutomorphicCompactFamily_continuous_of_projective K hζ f
  intro qf
  have hq : IsOpenQuotientMap
      (Prod.map (id : ℂ → ℂ)
        (ProjGenLinGroup.mk : GL (Fin 2) (InfiniteAdeleRing K) → PGL(2, InfiniteAdeleRing K))) :=
    IsOpenQuotientMap.id.prodMap (sourceKPArchProjectiveProjection_isOpenQuotientMap K)
  exact hq.continuous_comp_iff.mp (hf qf)

end
end ArtinMatthews
