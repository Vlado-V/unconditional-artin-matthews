module

public import ArtinMatthews.SourceKPAdelicDefectLocalFinite
public import ArtinMatthews.SourceKPAdelicDefectTermContinuity


set_option backward.privateInPublic true
@[expose] public section

/-! Joint continuity of the literal compact defect on an arbitrary
archimedean matrix fiber. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Filter
open scoped NumberField AdeleRing MatrixGroups BigOperators Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

private theorem defectTerm_matrix_continuous (T : ℝ)
    (qf : SourceKPFiniteAdeleProjective K hζ) (c : SourceKPRationalBorelCoset K) :
    Continuous (fun p : ℂ × GL (Fin 2) (InfiniteAdeleRing K) =>
      sourceKPAdelicDefectTerm K hζ T p.1 (ProjGenLinGroup.mk p.2,qf) c) := by
  have hm : Continuous (fun p : ℂ × GL (Fin 2) (InfiniteAdeleRing K) =>
      (p.1,ProjGenLinGroup.mk p.2)) :=
    continuous_fst.prodMk (continuous_quot_mk.comp continuous_snd)
  simpa only [Function.comp_def] using
    (sourceKPAdelicDefectTerm_joint_arch_continuous K hζ T qf c).comp hm

theorem sourceKPAdelicCutoffCasimirDefect_joint_matrix_continuous {T : ℝ} (hT : 0 < T)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun p : ℂ × GL (Fin 2) (InfiniteAdeleRing K) =>
      sourceKPAdelicCutoffCasimirDefect K hζ T p.1 (ProjGenLinGroup.mk p.2,qf)) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  obtain ⟨I,hI,hzero⟩ := sourceKPAdelicDefectTerm_locally_finite K hζ hT qf p₀.2
  have hc : Continuous (fun p : ℂ × GL (Fin 2) (InfiniteAdeleRing K) =>
      (InfinitePlace.nrComplexPlaces K : ℂ)*∑ c ∈ hI.toFinset,
        sourceKPAdelicDefectTerm K hζ T p.1 (ProjGenLinGroup.mk p.2,qf) c) := by
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro c _
    exact defectTerm_matrix_continuous K hζ T qf c
  apply hc.continuousAt.congr_of_eventuallyEq
  have hn := (continuous_snd.tendsto p₀).eventually hzero
  filter_upwards [hn] with p hp
  rw [sourceKPAdelicCutoffCasimirDefect_radial_sum K hζ hT]
  congr 1
  apply tsum_eq_sum
  intro c hci
  exact hp p.1 c (by simpa only [Set.Finite.mem_toFinset] using hci)

end
end ArtinMatthews
