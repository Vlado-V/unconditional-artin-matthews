module

public import ArtinMatthews.SourceKPAutomorphicMeasureChoice
public import ArtinMatthews.SourceKPAutomorphicComponentMeasure
public import ArtinMatthews.SourceKPAutomorphicComponentTopology
public import ArtinMatthews.FiniteIsotropyQuotientMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! Injective full-frame arithmetic charts carry the chosen automorphic measure. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing ENNReal Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

variable (μ : Measure (PGL(2, InfiniteAdeleRing K))) [μ.IsMulLeftInvariant]

theorem sourceKPAutomorphicMeasure_injective_chart (b : SourceKPFiniteLevelFiber K hζ)
    (A : Set (PGL(2, InfiniteAdeleRing K))) (hA : MeasurableSet A)
    (hinj : Set.InjOn (sourceKPArchComponentPoint K hζ b) A) :
    sourceKPAutomorphicMeasure K hζ μ (sourceKPArchComponentPoint K hζ b '' A) = μ A := by
  let j := sourceKPArchComponentPoint K hζ b
  let q := sourceKPArchComponentQuotientMap K hζ b
  let e := sourceKPArchComponentEmbedding K hζ b
  have hj : MeasurableSet (j '' A) := hA.image_of_continuousOn_injOn
    (sourceKPArchComponentPoint_continuous K hζ b).continuousOn hinj
  have he : e ⁻¹' (j '' A) = q '' A := by
    ext x
    constructor
    · rintro ⟨g,hg,hgx⟩
      exact ⟨g,hg,(sourceKPArchComponentEmbedding K hζ b).injective hgx⟩
    · rintro ⟨g,hg,rfl⟩
      exact ⟨g,hg,rfl⟩
  have hq : MeasurableSet (q '' A) := by
    rw [← he]
    exact hj.preimage (sourceKPArchComponentEmbedding_measurable K hζ b)
  have hsub : j '' A ⊆ sourceKPAutomorphicComponentSet K hζ (sourceKPFiniteOrbitMk K hζ b) := by
    rintro _ ⟨g,_,rfl⟩
    exact sourceKPAutomorphicFiniteOrbit_embedding K hζ b (q g)
  have hstable : ∀ h : (⊥ : Subgroup (sourceKPArchComponentSubgroup K hζ b)),
      ∀ x ∈ A, (h : sourceKPArchComponentSubgroup K hζ b) • x ∈ A := by
    intro h x hx
    have hh : (h : sourceKPArchComponentSubgroup K hζ b) = 1 := h.property
    simpa only [hh, one_smul] using hx
  have hsep : ∀ γ : sourceKPArchComponentSubgroup K hζ b,
      ∀ x ∈ A, γ • x ∈ A → γ ∈ (⊥ : Subgroup (sourceKPArchComponentSubgroup K hζ b)) := by
    intro γ x hx hγx
    have hqx : q (γ • x) = q x := by
      apply Quotient.sound
      exact MulAction.mem_orbit_iff.mpr ⟨γ,rfl⟩
    have hjx : j (γ • x) = j x := congrArg e hqx
    have hxx := hinj hγx hx hjx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact mul_right_cancel (hxx.trans (one_mul x).symm)
  calc
    sourceKPAutomorphicMeasure K hζ μ (j '' A) =
        (sourceKPAutomorphicMeasure K hζ μ).restrict
          (sourceKPAutomorphicComponentSet K hζ (sourceKPFiniteOrbitMk K hζ b)) (j '' A) := by
      rw [Measure.restrict_apply hj, inter_eq_left.mpr hsub]
    _ = sourceKPArchComponentPushMeasure K hζ b μ (j '' A) := by
      rw [sourceKPAutomorphicMeasure_restrict_component,
        ← sourceKPArchComponentPushMeasure_eq_component]
    _ = sourceKPArchComponentQuotientMeasure K hζ b μ (q '' A) := by
      rw [sourceKPArchComponentPushMeasure, Measure.map_apply
        (sourceKPArchComponentEmbedding_measurable K hζ b) hj, he]
    _ = μ A := by
      have hm := sourceFiniteSlice_quotient_measure μ
        (sourceKPArchComponentQuotientMeasure K hζ b μ)
        (⊥ : Subgroup (sourceKPArchComponentSubgroup K hζ b))
        (sourceKPArchComponentFundamentalDomain_isFundamental K hζ b μ)
        A hA hq hstable hsep
      simpa only [q, sourceKPArchComponentQuotientMap, QuotientGroup.rightRel, Subgroup.card_bot,
        Nat.cast_one, inv_one, one_mul] using hm

end
end ArtinMatthews
