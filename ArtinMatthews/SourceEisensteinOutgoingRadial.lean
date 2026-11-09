module

public import ArtinMatthews.SourceEisensteinOutgoingHeight
public import ArtinMatthews.SourceKPRadialHighFlow


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine outgoing term has its exact norm scaling under the actual
balanced high-cusp radial flow. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicTraceIntertwiner_norm_radial {s : ℂ} (hs : 0 < s.re)
    (t : ℝ) (a : PGL(2, InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ) :
    ‖sourceKPAdelicTraceIntertwiner K hζ s (sourceKPArchRadialFlow K hζ t a,qf)‖ =
      sourceKPRadialHeightScale K t ^ (1 / 2 - s.re) *
        ‖sourceKPAdelicTraceIntertwiner K hζ s (a,qf)‖ := by
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective a
  rw [sourceKPArchRadialFlow_mk, sourceKPAdelicTraceIntertwiner_norm_height K hζ hs,
    sourceKPAdelicTraceIntertwiner_norm_height K hζ hs, sourceKPArchRadialFlowMatrix_height,
    Real.mul_rpow (Real.exp_pos _).le (by
      unfold sourceKPArchMatrixHeight
      exact Finset.prod_nonneg (fun _ _ => pow_nonneg (SourceArchJacquet.sourceArchHeight_pos _).le _))]
  change _ = Real.exp _ ^ (1 / 2 - s.re) * _
  ring

end
end ArtinMatthews
