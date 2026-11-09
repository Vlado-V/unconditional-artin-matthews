module

public import ArtinMatthews.SourceKPAdelicParameterDerivative
public import ArtinMatthews.SourceAdelicHeightFibers
public import ArtinMatthews.SourceArchSectionContinuity


set_option backward.privateInPublic true
@[expose] public section

/-! Joint spectral and archimedean continuity of the actual flat
section and its literal parameter derivative. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCompactScalar_flat_cover (s : ℂ) (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCompactScalar K hζ s q =
      Complex.exp (s*(Real.log (sourceKPAdelicCoverHeight K hζ q) : ℂ))*
        sourceKPAdelicCompactScalar K hζ 0 q := by
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  have hh : sourceKPAdelicCoverHeight K hζ q = sourceKPAdelicHeight K hζ g := by
    unfold sourceKPAdelicCoverHeight
    rw [← hg,sourceKPAdelicHeightOnProjective_mk]
  rw [hh]
  exact sourceKPAdelicCompactScalar_flat K hζ s q g hg.symm

theorem sourceKPAdelicCompactScalar_arch_continuous (s : ℂ)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun a : PGL(2,InfiniteAdeleRing K) => sourceKPAdelicCompactScalar K hζ s (a,qf)) := by
  apply (QuotientGroup.isQuotientMap_mk
    (Subgroup.center (GL (Fin 2) (InfiniteAdeleRing K)))).continuous_iff.mpr
  exact sourceArchCompactScalar_continuous K hζ s qf

theorem sourceKPAdelicCompactScalar_joint_arch_continuous
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun p : ℂ × PGL(2,InfiniteAdeleRing K) =>
      sourceKPAdelicCompactScalar K hζ p.1 (p.2,qf)) := by
  have hl : Continuous (fun a : PGL(2,InfiniteAdeleRing K) =>
      Real.log (sourceKPAdelicCoverHeight K hζ (a,qf))) :=
    (sourceKPAdelicCoverHeight_arch_continuous K hζ qf).log
      (fun a => (sourceKPAdelicCoverHeight_pos K hζ (a,qf)).ne')
  have he : (fun p : ℂ × PGL(2,InfiniteAdeleRing K) =>
      sourceKPAdelicCompactScalar K hζ p.1 (p.2,qf)) = fun p =>
        Complex.exp (p.1*(Real.log (sourceKPAdelicCoverHeight K hζ (p.2,qf)) : ℂ))*
          sourceKPAdelicCompactScalar K hζ 0 (p.2,qf) :=
    funext (fun p => sourceKPAdelicCompactScalar_flat_cover K hζ p.1 (p.2,qf))
  rw [he]
  exact (Complex.continuous_exp.comp (continuous_fst.mul
    (Complex.continuous_ofReal.comp (hl.comp continuous_snd)))).mul
      ((sourceKPAdelicCompactScalar_arch_continuous K hζ 0 qf).comp continuous_snd)

def sourceKPAdelicCompactScalarParameterDerivative (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) : ℂ :=
  (Real.log (sourceKPAdelicCoverHeight K hζ q) : ℂ)*sourceKPAdelicCompactScalar K hζ s q

theorem sourceKPAdelicCompactScalarParameterDerivative_hasDerivAt (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) :
    HasDerivAt (fun z => sourceKPAdelicCompactScalar K hζ z q)
      (sourceKPAdelicCompactScalarParameterDerivative K hζ s q) s := by
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  have hh : sourceKPAdelicCoverHeight K hζ q = sourceKPAdelicHeight K hζ g := by
    unfold sourceKPAdelicCoverHeight
    rw [← hg,sourceKPAdelicHeightOnProjective_mk]
  simpa only [sourceKPAdelicCompactScalarParameterDerivative,hh] using
    sourceKPAdelicCompactScalar_hasDerivAt K hζ s q g hg.symm

theorem sourceKPAdelicCompactScalarParameterDerivative_joint_arch_continuous
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun p : ℂ × PGL(2,InfiniteAdeleRing K) =>
      sourceKPAdelicCompactScalarParameterDerivative K hζ p.1 (p.2,qf)) := by
  have hl := (sourceKPAdelicCoverHeight_arch_continuous K hζ qf).log
    (fun a => (sourceKPAdelicCoverHeight_pos K hζ (a,qf)).ne')
  exact (Complex.continuous_ofReal.comp (hl.comp continuous_snd)).mul
    (sourceKPAdelicCompactScalar_joint_arch_continuous K hζ qf)

end
end ArtinMatthews
