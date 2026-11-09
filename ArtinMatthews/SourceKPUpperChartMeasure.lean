module

public import ArtinMatthews.FiniteIsotropyChartMeasure
public import ArtinMatthews.SourceKPUpperQuotientMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite-isotropy hyperbolic charts retain their full stabilizer weight. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Topology
open scoped NumberField MatrixGroups AdeleRing Classical ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPArithmeticUpperMeasure_slice (b : SourceKPFiniteLevelFiber K hζ)
    (H : Subgroup (sourceKPArchComponentSubgroup K hζ b)) [Finite H]
    (U : Set (SourceKPArchUpperHalfSpace K)) (hU : MeasurableSet U)
    (himage : MeasurableSet (Quotient.mk
      (MulAction.orbitRel (sourceKPArchComponentSubgroup K hζ b) (SourceKPArchUpperHalfSpace K)) '' U))
    (hstable : ∀ h : H, ∀ x ∈ U, (h : sourceKPArchComponentSubgroup K hζ b) • x ∈ U)
    (hsep : ∀ γ : sourceKPArchComponentSubgroup K hζ b, ∀ x ∈ U, γ • x ∈ U → γ ∈ H) :
    (sourceKPArithmeticUpperMeasure K hζ b).restrict (Quotient.mk _ '' U) =
      (Nat.card H : ℝ≥0∞)⁻¹ • ((sourceKPArchHyperbolicMeasure K).restrict U).map (Quotient.mk _) := by
  exact sourceFiniteSlice_projection_measure (sourceKPArchHaar K hζ)
    (sourceKPArchComponentQuotientMeasure K hζ b (sourceKPArchHaar K hζ))
    (sourceKPArchHyperbolicMeasure K) (sourceKPUpperProjection K hζ)
    (sourceKPUpperProjection_preserving K hζ) (sourceKPUpperProjection_equivariant K hζ b)
    (sourceKPUpperQuotientProjection K hζ b) (sourceKPUpperQuotientProjection_measurable K hζ b)
    (sourceKPUpperQuotientProjection_mk K hζ b) H
    (sourceKPArchComponentFundamentalDomain_isFundamental K hζ b (sourceKPArchHaar K hζ))
    U hU himage hstable hsep


variable (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)
    (c : SourceFiniteIsotropyChart (sourceKPArchComponentSubgroup K hζ b)
      (SourceKPArchUpperHalfSpace K) p)

theorem sourceKPUpperChart_measurePreserving :
    MeasurePreserving (sourceFiniteChartProjection c)
      ((Nat.card (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) p) : ℝ≥0∞)⁻¹ •
        sourceFiniteChartDomainMeasure c (sourceKPArchHyperbolicMeasure K))
      ((sourceKPArithmeticUpperMeasure K hζ b).restrict
        (Set.range (sourceFiniteChartProjection c))) :=
  sourceFiniteChartProjection_measurePreserving (sourceKPArchHaar K hζ)
    (sourceKPArchComponentQuotientMeasure K hζ b (sourceKPArchHaar K hζ))
    (sourceKPArchHyperbolicMeasure K) (sourceKPUpperProjection K hζ)
    (sourceKPUpperProjection_preserving K hζ) (sourceKPUpperProjection_equivariant K hζ b)
    (sourceKPUpperQuotientProjection K hζ b) (sourceKPUpperQuotientProjection_measurable K hζ b)
    (sourceKPUpperQuotientProjection_mk K hζ b)
    (sourceKPArchComponentFundamentalDomain_isFundamental K hζ b (sourceKPArchHaar K hζ)) c

include c in
theorem sourceKPUpperChart_weight_pos :
    0 < (Nat.card (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) p) : ℝ≥0∞)⁻¹ ∧
      (Nat.card (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) p) : ℝ≥0∞)⁻¹ ≠ ⊤ :=
  sourceFiniteChart_weight_pos c


instance sourceKPUpperChartDomain_finite :
    IsFiniteMeasure (sourceFiniteChartDomainMeasure c (sourceKPArchHyperbolicMeasure K)) where
  measure_univ_lt_top := by
    change (sourceKPArchHyperbolicMeasure K).comap
      (Subtype.val : ↥(c.domain : Set (SourceKPArchUpperHalfSpace K)) →
        SourceKPArchUpperHalfSpace K) Set.univ < ⊤
    rw [comap_subtype_coe_apply (s := (c.domain : Set (SourceKPArchUpperHalfSpace K)))
      c.isOpen_domain.measurableSet]
    simp only [Set.image_univ, Subtype.range_coe]
    exact (measure_mono (subset_closure : (c.domain : Set (SourceKPArchUpperHalfSpace K)) ⊆
      closure (c.domain : Set (SourceKPArchUpperHalfSpace K)))).trans_lt
        c.isCompact_closure.measure_lt_top

end
end ArtinMatthews
