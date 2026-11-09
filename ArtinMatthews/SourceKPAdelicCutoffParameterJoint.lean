module

public import ArtinMatthews.SourceKPAdelicCutoffContinuity
public import ArtinMatthews.SourceKPAdelicSectionParameterContinuity


set_option backward.privateInPublic true
@[expose] public section

/-! The literal parameter derivative of the cusp cutoff is jointly continuous
on every archimedean matrix fiber. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Filter
open scoped NumberField AdeleRing MatrixGroups BigOperators Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

private def cutoffSummandParameterDerivative (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (c : SourceKPRationalBorelCoset K) : ℂ :=
  (Real.log (sourceKPAdelicRationalHeight K hζ q c) : ℂ) *
    sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T s) q c

private theorem cutoffSummand_hasDerivAt (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (c : SourceKPRationalBorelCoset K) :
    HasDerivAt
      (fun z => sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T z) q c)
      (cutoffSummandParameterDerivative K hζ T s q c) s := by
  induction c using Quotient.inductionOn with
  | _ γ =>
    let a := sourceKPAdelicProjectiveRationalLift K hζ γ * q
    let H := sourceKPAdelicCoverHeight K hζ a
    let w : ℂ := sourceKPAdelicHeightCutoff T H
    change HasDerivAt (fun z => w * sourceKPAdelicCompactScalar K hζ z a)
      ((Real.log H : ℂ) * (w * sourceKPAdelicCompactScalar K hζ s a)) s
    have h := (sourceKPAdelicCompactScalarParameterDerivative_hasDerivAt K hζ s a).const_mul w
    change HasDerivAt (fun z => w * sourceKPAdelicCompactScalar K hζ z a)
      (w * ((Real.log H : ℂ) * sourceKPAdelicCompactScalar K hζ s a)) s at h
    simpa only [mul_left_comm] using h

def sourceKPAdelicCutoffEisensteinParameterDerivative (T : ℝ) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) : ℂ :=
  deriv (fun z => sourceKPAdelicCutoffEisenstein K hζ T z q) s

theorem sourceKPAdelicCutoffEisenstein_hasDerivAt {T : ℝ} (hT : 0 < T) (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) :
    HasDerivAt (fun z => sourceKPAdelicCutoffEisenstein K hζ T z q)
      (sourceKPAdelicCutoffEisensteinParameterDerivative K hζ T s q) s :=
  (sourceKPAdelicCutoffEisenstein_entire K hζ hT q s).hasDerivAt

private theorem cutoffDerivative_eq_sum (T : ℝ) (q : SourceKPAdelicProjective K hζ)
    (I : Finset (SourceKPRationalBorelCoset K))
    (hz : ∀ z c, c ∉ I →
      sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T z) q c = 0) (s : ℂ) :
    sourceKPAdelicCutoffEisensteinParameterDerivative K hζ T s q =
      ∑ c ∈ I, cutoffSummandParameterDerivative K hζ T s q c := by
  have he : (fun z => sourceKPAdelicCutoffEisenstein K hζ T z q) =
      fun z => ∑ c ∈ I,
        sourceKPAdelicRationalSummand K hζ (sourceKPAdelicCutoffSeed K hζ T z) q c := by
    funext z
    exact tsum_eq_sum (hz z)
  unfold sourceKPAdelicCutoffEisensteinParameterDerivative
  rw [he]
  exact (HasDerivAt.fun_sum (fun c _ => cutoffSummand_hasDerivAt K hζ T s q c)).deriv

private theorem cutoffSummandDerivative_matrix_continuous (T : ℝ)
    (qf : SourceKPFiniteAdeleProjective K hζ) (c : SourceKPRationalBorelCoset K) :
    Continuous (fun p : ℂ × GL (Fin 2) (InfiniteAdeleRing K) =>
      cutoffSummandParameterDerivative K hζ T p.1 (ProjGenLinGroup.mk p.2,qf) c) := by
  have hH := sourceKPAdelicRationalHeight_arch_continuous K hζ qf c
  have hlog := hH.log (fun a => (sourceKPAdelicRationalHeight_pos K hζ (a,qf) c).ne')
  have h : Continuous (fun p : ℂ × PGL(2,InfiniteAdeleRing K) =>
      cutoffSummandParameterDerivative K hζ T p.1 (p.2,qf) c) :=
    (Complex.continuous_ofReal.comp (hlog.comp continuous_snd)).mul
      (sourceKPAdelicCutoffSummand_joint_arch_continuous K hζ T qf c)
  have hm : Continuous (fun p : ℂ × GL (Fin 2) (InfiniteAdeleRing K) =>
      (p.1,ProjGenLinGroup.mk p.2)) :=
    continuous_fst.prodMk (continuous_quot_mk.comp continuous_snd)
  simpa only [Function.comp_def] using h.comp hm

theorem sourceKPAdelicCutoffEisensteinParameterDerivative_joint_matrix_continuous
    {T : ℝ} (hT : 0 < T) (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun p : ℂ × GL (Fin 2) (InfiniteAdeleRing K) =>
      sourceKPAdelicCutoffEisensteinParameterDerivative K hζ T p.1 (ProjGenLinGroup.mk p.2,qf)) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  obtain ⟨I,hI,hzero⟩ := sourceKPAdelicCutoffSummand_locally_finite K hζ hT qf p₀.2
  have hc : Continuous (fun p : ℂ × GL (Fin 2) (InfiniteAdeleRing K) =>
      ∑ c ∈ hI.toFinset,
        cutoffSummandParameterDerivative K hζ T p.1 (ProjGenLinGroup.mk p.2,qf) c) := by
    apply continuous_finsetSum
    intro c _
    exact cutoffSummandDerivative_matrix_continuous K hζ T qf c
  apply hc.continuousAt.congr_of_eventuallyEq
  have hn := (continuous_snd.tendsto p₀).eventually hzero
  filter_upwards [hn] with p hp
  exact cutoffDerivative_eq_sum K hζ T _ hI.toFinset
    (fun z c hci => hp z c (by simpa only [Set.Finite.mem_toFinset] using hci)) p.1

end
end ArtinMatthews
