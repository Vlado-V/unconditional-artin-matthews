module

public import ArtinMatthews.SourceKPAutomorphicMeasure
public import ArtinMatthews.SourceKPArchComponentConjugacyMeasure


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPArchComponentSubgroup_rational (γ : PGL(2, K))
    (b : SourceKPFiniteLevelFiber K hζ) :
    sourceKPArchComponentSubgroup K hζ (γ • b) =
      sourceConjugateSubgroup (sourceKPArchComponentSubgroup K hζ b)
        (sourceKPRationalArchMap K hζ γ) := by
  unfold sourceKPArchComponentSubgroup sourceKPRationalFiniteStabilizer
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  simp only [sourceConjugateSubgroup, Subgroup.map_map]
  congr 1
  ext x
  simp [MonoidHom.comp_apply, MulAut.conj_apply]

def sourceKPArchComponentPushMeasure (b : SourceKPFiniteLevelFiber K hζ)
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) : Measure (SourceKPAutomorphicLevel K hζ) :=
  Measure.map (sourceKPArchComponentEmbedding K hζ b)
    (sourceKPArchComponentQuotientMeasure K hζ b μ)

theorem sourceKPArchComponent_rational_embedding (γ : PGL(2, K))
    (b : SourceKPFiniteLevelFiber K hζ) (q : SourceKPArchComponentQuotient K hζ b) :
    sourceKPArchComponentEmbedding K hζ (γ • b)
      (sourceKPArchComponentConjugacy K hζ b (γ • b) (sourceKPRationalArchMap K hζ γ)
        (sourceKPArchComponentSubgroup_rational K hζ γ b) q) =
      sourceKPArchComponentEmbedding K hζ b q := by
  induction q using Quotient.inductionOn with
  | _ a =>
    change sourceKPArchComponentEmbedding K hζ (γ • b)
      (sourceKPArchComponentConjugacy K hζ b (γ • b) (sourceKPRationalArchMap K hζ γ)
        (sourceKPArchComponentSubgroup_rational K hζ γ b)
        (sourceKPArchComponentQuotientMap K hζ b a)) = _
    rw [sourceKPArchComponentConjugacy_mk]
    apply Quotient.sound
    exact MulAction.mem_orbit_iff.mpr ⟨γ,rfl⟩

theorem sourceKPArchComponentPushMeasure_rational (γ : PGL(2, K))
    (b : SourceKPFiniteLevelFiber K hζ)
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) [μ.IsMulLeftInvariant] :
    sourceKPArchComponentPushMeasure K hζ (γ • b) μ =
      sourceKPArchComponentPushMeasure K hζ b μ := by
  have he := sourceKPArchComponentConjugacy_measurePreserving K hζ b (γ • b)
    (sourceKPRationalArchMap K hζ γ) (sourceKPArchComponentSubgroup_rational K hζ γ b) μ
  unfold sourceKPArchComponentPushMeasure
  rw [← he.map_eq, Measure.map_map (sourceKPArchComponentEmbedding_measurable K hζ _) he.measurable]
  congr 1
  funext q
  exact sourceKPArchComponent_rational_embedding K hζ γ b q

theorem sourceKPArchComponentPushMeasure_orbit (b c : SourceKPFiniteLevelFiber K hζ)
    (h : sourceKPFiniteOrbitMk K hζ b = sourceKPFiniteOrbitMk K hζ c)
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) [μ.IsMulLeftInvariant] :
    sourceKPArchComponentPushMeasure K hζ b μ = sourceKPArchComponentPushMeasure K hζ c μ := by
  obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h)
  rw [← hγ]
  exact sourceKPArchComponentPushMeasure_rational K hζ γ c μ

theorem sourceKPArchComponentPushMeasure_eq_component (b : SourceKPFiniteLevelFiber K hζ)
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) [μ.IsMulLeftInvariant] :
    sourceKPArchComponentPushMeasure K hζ b μ =
      sourceKPAutomorphicComponentMeasure K hζ μ (sourceKPFiniteOrbitMk K hζ b) := by
  apply sourceKPArchComponentPushMeasure_orbit K hζ
  exact (sourceKPFiniteOrbitRepresentative_spec K hζ _).symm

end
end ArtinMatthews
