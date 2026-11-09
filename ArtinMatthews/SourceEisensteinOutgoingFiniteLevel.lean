module

public import ArtinMatthews.SourceEisensteinNonconstantInvariance
public import ArtinMatthews.SourceEisensteinOutgoingHeight
public import ArtinMatthews.SourceArchSectionContinuity
public import ArtinMatthews.SourceKPFiniteLevelTopology


set_option backward.privateInPublic true
@[expose] public section

/-! The actual outgoing term descends continuously to the original finite level. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceArchSphericalProduct_continuous (s : ℂ) :
    Continuous (sourceArchSphericalProduct K hζ s) := by
  apply (QuotientGroup.isQuotientMap_mk (Subgroup.center (GL (Fin 2) (InfiniteAdeleRing K)))).continuous_iff.mpr
  exact sourceArchSphericalProduct_matrix_continuous K hζ s

theorem sourceKPAdelicTraceIntertwiner_arch_continuous {s : ℂ} (hs : 0 < s.re)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun a : PGL(2, InfiniteAdeleRing K) => sourceKPAdelicTraceIntertwiner K hζ s (a,qf)) := by
  have hc : Continuous (fun a : PGL(2, InfiniteAdeleRing K) =>
      ((Real.pi : ℂ) / s) ^ Fintype.card (InfinitePlace K) *
        sourceArchSphericalProduct K hζ (-s) a * sourceKPFiniteIntertwiner K hζ s qf) :=
    (continuous_const.mul (sourceArchSphericalProduct_continuous K hζ (-s))).mul continuous_const
  exact hc.congr (fun a => (sourceKPAdelicTraceIntertwiner_arch_formula K hζ hs (a,qf)).symm)

theorem sourceKPAdelicTraceIntertwiner_finite_right (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (k : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPAdelicTraceIntertwiner K hζ s (g * sourceKPFiniteDeepCoverLift K hζ k) =
      sourceKPAdelicTraceIntertwiner K hζ s g :=
  sourceKPAdelicTraceIntertwiner_deepCompact_right K hζ s g
    ⟨sourceKPFiniteDeepCoverLift K hζ k, ⟨sourceKPFiniteDeepIntoAdelic K hζ k, rfl⟩⟩

def sourceKPFiniteLevelOutgoingEisenstein (s : ℂ) : SourceKPFiniteLevelSpace K hζ → ℂ :=
  sourceKPFiniteLevelDescend K hζ (sourceKPAdelicTraceIntertwiner K hζ s)
    (sourceKPAdelicTraceIntertwiner_finite_right K hζ s)

theorem sourceKPFiniteLevelOutgoingEisenstein_mk (s : ℂ) (g : SourceKPAdelicProjective K hζ) :
    sourceKPFiniteLevelOutgoingEisenstein K hζ s (sourceKPFiniteLevelMk K hζ g) =
      sourceKPAdelicTraceIntertwiner K hζ s g := rfl

theorem sourceKPFiniteLevelOutgoingEisenstein_continuous {s : ℂ} (hs : 0 < s.re) :
    Continuous (sourceKPFiniteLevelOutgoingEisenstein K hζ s) :=
  sourceKPFiniteLevelDescend_continuous K hζ _ _
    (sourceKPAdelicTraceIntertwiner_arch_continuous K hζ hs)

end
end ArtinMatthews
