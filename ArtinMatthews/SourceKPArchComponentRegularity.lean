module

public import ArtinMatthews.SourceKPArchComponentIntegration
public import ArtinMatthews.SourceKPArchComponentBorel


set_option backward.privateInPublic true
@[expose] public section

/-! Local finiteness and open positivity of actual arithmetic quotient measures. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing Classical Pointwise ENNReal
noncomputable section

section ImageBound
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (ν : Measure (Quotient (QuotientGroup.rightRel Γ)))
    [QuotientMeasureEqMeasurePreimage (G := Γ) μ ν]

theorem sourceLeftQuotientMeasure_image_le {F : Set G}
    (hF : IsFundamentalDomain Γ F μ) (V : Set G)
    (hV : MeasurableSet (Quotient.mk (QuotientGroup.rightRel Γ) '' V)) :
    ν (Quotient.mk (QuotientGroup.rightRel Γ) '' V) ≤ μ V := by
  rw [hF.projection_respects_measure_apply ν hV]
  have he : (Quotient.mk (QuotientGroup.rightRel Γ)) ⁻¹'
      (Quotient.mk (QuotientGroup.rightRel Γ) '' V) = ⋃ γ : Γ, γ • V :=
    MulAction.quotient_preimage_image_eq_union_mul V (G := Γ)
  change μ (((Quotient.mk (QuotientGroup.rightRel Γ)) ⁻¹'
    (Quotient.mk (QuotientGroup.rightRel Γ) '' V)) ∩ F) ≤ μ V
  rw [he, iUnion_inter]
  exact (measure_iUnion_le _).trans_eq (hF.measure_eq_tsum V).symm

end ImageBound

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (b : SourceKPFiniteLevelFiber K hζ) (μ : Measure (PGL(2, InfiniteAdeleRing K)))
    [μ.IsMulLeftInvariant]

omit [μ.IsMulLeftInvariant] in
theorem sourceKPArchComponentQuotientMap_isOpenMap :
    IsOpenMap (sourceKPArchComponentQuotientMap K hζ b) := by
  exact MulAction.isOpenQuotientMap_quotientMk.isOpenMap

theorem sourceKPArchComponentQuotientMeasure_open_image_le
    (V : Set (PGL(2, InfiniteAdeleRing K))) (hV : IsOpen V) :
    sourceKPArchComponentQuotientMeasure K hζ b μ
      (sourceKPArchComponentQuotientMap K hζ b '' V) ≤ μ V :=
  sourceLeftQuotientMeasure_image_le (sourceKPArchComponentSubgroup K hζ b) μ
    (sourceKPArchComponentQuotientMeasure K hζ b μ)
    (sourceKPArchComponentFundamentalDomain_isFundamental K hζ b μ) V
    ((sourceKPArchComponentQuotientMap_isOpenMap K hζ b V hV).measurableSet)

instance sourceKPArchComponentQuotientMeasure_locallyFinite [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (sourceKPArchComponentQuotientMeasure K hζ b μ) where
  finiteAtNhds q := by
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    obtain ⟨V, hg, hV, hfinite⟩ := μ.exists_isOpen_measure_lt_top g
    refine ⟨sourceKPArchComponentQuotientMap K hζ b '' V, ?_, ?_⟩
    · exact (sourceKPArchComponentQuotientMap_isOpenMap K hζ b V hV).mem_nhds
        ⟨g, hg, rfl⟩
    · exact (sourceKPArchComponentQuotientMeasure_open_image_le K hζ b μ V hV).trans_lt hfinite

theorem sourceKPArchComponentQuotientMeasure_finite_on_compacts [IsLocallyFiniteMeasure μ]
    (C : Set (SourceKPArchComponentQuotient K hζ b)) (hC : IsCompact C) :
    sourceKPArchComponentQuotientMeasure K hζ b μ C < ⊤ := hC.measure_lt_top

instance sourceKPArchComponentQuotientMeasure_openPositive [μ.IsOpenPosMeasure] :
    (sourceKPArchComponentQuotientMeasure K hζ b μ).IsOpenPosMeasure where
  open_pos U hU hne := by
    let A := (sourceKPArchComponentQuotientMap K hζ b) ⁻¹' U
    have hA : IsOpen A := hU.preimage (sourceKPArchComponentQuotientMap_continuous K hζ b)
    have hAne : A.Nonempty := by
      obtain ⟨q, hq⟩ := hne
      obtain ⟨g, rfl⟩ := Quotient.exists_rep q
      exact ⟨g, hq⟩
    intro hzero
    apply hA.measure_ne_zero μ hAne
    apply (sourceKPArchComponentFundamentalDomain_isFundamental K hζ b μ).measure_zero_of_invariant A
    · intro γ
      ext g
      simp only [mem_smul_set_iff_inv_smul_mem, A, mem_preimage,
        sourceKPArchComponentQuotientMap_smul]
    · rw [← sourceKPArchComponentQuotientMeasure_apply K hζ b μ
        (sourceKPArchComponentFundamentalDomain K hζ b μ)
        (sourceKPArchComponentFundamentalDomain_isFundamental K hζ b μ) U hU.measurableSet]
      exact hzero

end
end ArtinMatthews
