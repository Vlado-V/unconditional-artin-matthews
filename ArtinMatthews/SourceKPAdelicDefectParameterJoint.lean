module

public import ArtinMatthews.SourceKPAdelicDefectJointContinuity
public import ArtinMatthews.SourceKPAdelicDefectTermDerivative


set_option backward.privateInPublic true
@[expose] public section

/-! The literal parameter derivative of the actual defect and its
joint continuity on every archimedean matrix fiber. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Filter
open scoped NumberField AdeleRing MatrixGroups BigOperators Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicCutoffDefectParameterDerivative (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) : ℂ :=
  deriv (fun z => sourceKPAdelicCutoffCasimirDefect K hζ T z q) s

theorem sourceKPAdelicCutoffCasimirDefect_hasDerivAt {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) :
    HasDerivAt (fun z => sourceKPAdelicCutoffCasimirDefect K hζ T z q)
      (sourceKPAdelicCutoffDefectParameterDerivative K hζ T s q) s :=
  (sourceKPAdelicCutoffCasimirDefect_entire K hζ hT q s).hasDerivAt

private theorem defectParameterDerivative_eq_sum {T : ℝ} (hT : 0 < T)
    (q : SourceKPAdelicProjective K hζ) (I : Finset (SourceKPRationalBorelCoset K))
    (hz : ∀ z c, c ∉ I → sourceKPAdelicDefectTerm K hζ T z q c = 0) (s : ℂ) :
    sourceKPAdelicCutoffDefectParameterDerivative K hζ T s q =
      (InfinitePlace.nrComplexPlaces K : ℂ)*∑ c ∈ I,
        sourceKPAdelicDefectTermDerivative K hζ T s q c := by
  have he : (fun z => sourceKPAdelicCutoffCasimirDefect K hζ T z q) =
      fun z => (InfinitePlace.nrComplexPlaces K : ℂ)*∑ c ∈ I, sourceKPAdelicDefectTerm K hζ T z q c := by
    funext z
    rw [sourceKPAdelicCutoffCasimirDefect_radial_sum K hζ hT]
    congr 1
    exact tsum_eq_sum (hz z)
  unfold sourceKPAdelicCutoffDefectParameterDerivative
  rw [he]
  exact ((HasDerivAt.fun_sum (fun c _ => sourceKPAdelicDefectTerm_hasDerivAt K hζ T s q c)).const_mul
    (InfinitePlace.nrComplexPlaces K : ℂ)).deriv

private theorem defectTermDerivative_matrix_continuous (T : ℝ)
    (qf : SourceKPFiniteAdeleProjective K hζ) (c : SourceKPRationalBorelCoset K) :
    Continuous (fun p : ℂ × GL (Fin 2) (InfiniteAdeleRing K) =>
      sourceKPAdelicDefectTermDerivative K hζ T p.1 (ProjGenLinGroup.mk p.2,qf) c) := by
  have hm : Continuous (fun p : ℂ × GL (Fin 2) (InfiniteAdeleRing K) =>
      (p.1,ProjGenLinGroup.mk p.2)) :=
    continuous_fst.prodMk (continuous_quot_mk.comp continuous_snd)
  simpa only [Function.comp_def] using
    (sourceKPAdelicDefectTermDerivative_joint_arch_continuous K hζ T qf c).comp hm

theorem sourceKPAdelicCutoffDefectParameterDerivative_joint_matrix_continuous {T : ℝ} (hT : 0 < T)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun p : ℂ × GL (Fin 2) (InfiniteAdeleRing K) =>
      sourceKPAdelicCutoffDefectParameterDerivative K hζ T p.1 (ProjGenLinGroup.mk p.2,qf)) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  obtain ⟨I,hI,hzero⟩ := sourceKPAdelicDefectTerm_locally_finite K hζ hT qf p₀.2
  have hc : Continuous (fun p : ℂ × GL (Fin 2) (InfiniteAdeleRing K) =>
      (InfinitePlace.nrComplexPlaces K : ℂ)*∑ c ∈ hI.toFinset,
        sourceKPAdelicDefectTermDerivative K hζ T p.1 (ProjGenLinGroup.mk p.2,qf) c) := by
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro c _
    exact defectTermDerivative_matrix_continuous K hζ T qf c
  apply hc.continuousAt.congr_of_eventuallyEq
  have hn := (continuous_snd.tendsto p₀).eventually hzero
  filter_upwards [hn] with p hp
  exact defectParameterDerivative_eq_sum K hζ hT _ hI.toFinset
    (fun z c hci => hp z c (by simpa only [Set.Finite.mem_toFinset] using hci)) p.1

end
end ArtinMatthews
