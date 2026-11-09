module

public import ArtinMatthews.SourceKPCuspLevelCover
public import ArtinMatthews.SourceKPCuspDirections


set_option backward.privateInPublic true
@[expose] public section

/-! The principal torus cover is continuous and has the actual compact unipotent
    orbit in the original finite-level automorphic quotient as its image. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Module Module.Free Matrix Topology
open scoped NumberField MatrixGroups AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => mixedEmbedding.mixedSpace K
local instance : TopologicalSpace
    (SourceKPFiniteAdeleProjective K hζ ⧸ sourceKPFiniteLevelSubgroup K hζ) :=
  sourceKPFiniteLevelFiber_topology K hζ
local instance : TopologicalSpace
    (Quotient (MulAction.orbitRel (PGL(2, K)) (SourceKPFiniteLevelSpace K hζ))) :=
  sourceKPAutomorphicLevel_topology K hζ

omit [NumberField K] in
lemma sourceKPCuspUpperArch_continuous :
    Continuous (sourceKPUpperMatrix (InfiniteAdeleRing K)) := by
  have hc : Continuous (fun x : InfiniteAdeleRing K =>
      (sourceKPUpperMatrix (InfiniteAdeleRing K) x : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) := by
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_id
    · exact continuous_const
    · exact continuous_const
  have hi (x : InfiniteAdeleRing K) :
      (sourceKPUpperMatrix (InfiniteAdeleRing K) x)⁻¹ = sourceKPUpperMatrix (InfiniteAdeleRing K) (-x) := by
    apply inv_eq_iff_mul_eq_one.mpr
    rw [← sourceKPUpperMatrix_add, add_neg_cancel, sourceKPUpperMatrix_zero]
  apply Units.continuous_iff.mpr
  refine ⟨hc, ?_⟩
  simpa only [hi, Function.comp_def] using hc.comp continuous_neg

lemma sourceKPCuspOrbit_arch_eq (g : SourceKPAdelicProjective K hζ) (x : E) :
    sourceKPCuspOrbit K hζ g
        (OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction.mixedAdelicAdd K x) =
      Quotient.mk _
        (ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)) * g.1,
          (QuotientGroup.mk g.2 : SourceKPFiniteLevelFiber K hζ)) := by
  change Quotient.mk _
    (ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)) * g.1,
      QuotientGroup.mk (sourceKPFiniteAdeleUpperLift K hζ 0 * g.2)) = _
  rw [sourceKPFiniteAdeleUpperLift_zero, one_mul]

lemma sourceKPCuspOrbit_arch_continuous (g : SourceKPAdelicProjective K hζ) :
    Continuous (fun x : E => sourceKPCuspOrbit K hζ g
      (OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction.mixedAdelicAdd K x)) := by
  simp_rw [sourceKPCuspOrbit_arch_eq]
  have hmk : Continuous
      (ProjGenLinGroup.mk : GL (Fin 2) (InfiniteAdeleRing K) → PGL(2, InfiniteAdeleRing K)) :=
    QuotientGroup.continuous_mk
  have harch : Continuous (fun x : E =>
      (ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)) : PGL(2, InfiniteAdeleRing K)) * g.1) :=
    (hmk.comp ((sourceKPCuspUpperArch_continuous K).comp
      (OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph K).symm.continuous)).mul continuous_const
  have hq : Continuous (fun y : SourceKPFiniteLevelSpace K hζ =>
      (Quotient.mk _ y : SourceKPAutomorphicLevel K hζ)) := continuous_quotient_mk'
  exact hq.comp (harch.prodMk continuous_const)

variable (d : 𝓞 K) (g : SourceKPAdelicProjective K hζ)
variable (hperiod : ∀ t ∈ sourceKPCuspFiniteIdeal K d,
  ∃ k : sourceKPFiniteDeepMatrixGroup K,
    g⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * g =
      sourceKPFiniteDeepCoverLift K hζ k)
include hperiod

lemma sourceKPCuspLevelCover_range :
    Set.range (sourceKPCuspLevelCover K hζ d g hperiod) = Set.range (sourceKPCuspOrbit K hζ g) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨QuotientAddGroup.mk a, rfl⟩

lemma sourceKPCuspLevelCover_continuous (hd : d ≠ 0) :
    Continuous (sourceKPCuspLevelCover K hζ d g hperiod) := by
  apply ((sourceKPCuspArchQuotientMap_isOpenMap K d hd).isQuotientMap
    (sourceKPCuspArchQuotientMap_continuous K d)
    (sourceKPCuspArchQuotientMap_surjective K d hd)).continuous_iff.mpr
  exact sourceKPCuspOrbit_arch_continuous K hζ g

def sourceKPCuspLevelCoverContinuous (hd : d ≠ 0) :
    C(SourceKPCuspPrincipalQuotient K d, SourceKPAutomorphicLevel K hζ) :=
  ⟨sourceKPCuspLevelCover K hζ d g hperiod, sourceKPCuspLevelCover_continuous K hζ d g hperiod hd⟩

omit hperiod in
theorem sourceKPCuspOrbit_isCompact : IsCompact (Set.range (sourceKPCuspOrbit K hζ g)) := by
  obtain ⟨d, hd, hperiod⟩ := sourceKPAdelicCuspFiniteLevelPeriod K hζ g
  let := sourceKPCuspPrincipalQuotient_compact K d hd
  rw [← sourceKPCuspLevelCover_range K hζ d g hperiod]
  exact isCompact_range (sourceKPCuspLevelCover_continuous K hζ d g hperiod hd)

omit hperiod in
theorem sourceKPCusp_continuous_principal_cover (g : SourceKPAdelicProjective K hζ) :
    ∃ d : 𝓞 K, d ≠ 0 ∧
      ∃ f : C(SourceKPCuspPrincipalQuotient K d, SourceKPAutomorphicLevel K hζ),
        ∀ a : 𝔸[K], f (QuotientAddGroup.mk a) = sourceKPCuspOrbit K hζ g a := by
  obtain ⟨d, hd, hperiod⟩ := sourceKPAdelicCuspFiniteLevelPeriod K hζ g
  exact ⟨d, hd, sourceKPCuspLevelCoverContinuous K hζ d g hperiod hd, fun _ => rfl⟩

end
end ArtinMatthews
