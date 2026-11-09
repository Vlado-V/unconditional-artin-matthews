module

public import ArtinMatthews.SourceKPArchComponentMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! Quotient integration and unfolding for the literal left arithmetic action. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing Classical ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (b : SourceKPFiniteLevelFiber K hζ) (μ : Measure (PGL(2, InfiniteAdeleRing K)))
    [μ.IsMulLeftInvariant]

theorem sourceKPArchComponent_quotient_lintegral
    (D : Set (PGL(2, InfiniteAdeleRing K)))
    (hD : IsFundamentalDomain (sourceKPArchComponentSubgroup K hζ b) D μ)
    (f : SourceKPArchComponentQuotient K hζ b → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂sourceKPArchComponentQuotientMeasure K hζ b μ =
      ∫⁻ g in D, f (sourceKPArchComponentQuotientMap K hζ b g) ∂μ := by
  rw [sourceKPArchComponentQuotientMeasure_independent K hζ b μ D hD]
  exact lintegral_map hf (sourceKPArchComponentQuotientMap_measurable K hζ b)

theorem sourceKPArchComponent_lintegral_independent
    (D : Set (PGL(2, InfiniteAdeleRing K)))
    (hD : IsFundamentalDomain (sourceKPArchComponentSubgroup K hζ b) D μ)
    (f : PGL(2, InfiniteAdeleRing K) → ℝ≥0∞)
    (hf : ∀ γ : sourceKPArchComponentSubgroup K hζ b, ∀ g, f (γ • g) = f g) :
    ∫⁻ g in sourceKPArchComponentFundamentalDomain K hζ b μ, f g ∂μ =
      ∫⁻ g in D, f g ∂μ :=
  (sourceKPArchComponentFundamentalDomain_isFundamental K hζ b μ).setLIntegral_eq hD f hf

theorem sourceKPArchComponent_lintegral_unfold (f : PGL(2, InfiniteAdeleRing K) → ℝ≥0∞) :
    ∫⁻ g, f g ∂μ =
      ∑' γ : sourceKPArchComponentSubgroup K hζ b,
        ∫⁻ g in sourceKPArchComponentFundamentalDomain K hζ b μ, f (γ • g) ∂μ :=
  (sourceKPArchComponentFundamentalDomain_isFundamental K hζ b μ).lintegral_eq_tsum'' f

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sourceKPArchComponent_quotient_integral
    (D : Set (PGL(2, InfiniteAdeleRing K)))
    (hD : IsFundamentalDomain (sourceKPArchComponentSubgroup K hζ b) D μ)
    (f : SourceKPArchComponentQuotient K hζ b → E)
    (hf : AEStronglyMeasurable f (sourceKPArchComponentQuotientMeasure K hζ b μ)) :
    ∫ x, f x ∂sourceKPArchComponentQuotientMeasure K hζ b μ =
      ∫ g in D, f (sourceKPArchComponentQuotientMap K hζ b g) ∂μ := by
  rw [sourceKPArchComponentQuotientMeasure_independent K hζ b μ D hD] at hf ⊢
  exact integral_map (sourceKPArchComponentQuotientMap_measurable K hζ b).aemeasurable hf

theorem sourceKPArchComponent_integral_independent
    (D : Set (PGL(2, InfiniteAdeleRing K)))
    (hD : IsFundamentalDomain (sourceKPArchComponentSubgroup K hζ b) D μ)
    (f : PGL(2, InfiniteAdeleRing K) → E)
    (hf : ∀ γ : sourceKPArchComponentSubgroup K hζ b, ∀ g, f (γ • g) = f g) :
    ∫ g in sourceKPArchComponentFundamentalDomain K hζ b μ, f g ∂μ = ∫ g in D, f g ∂μ :=
  (sourceKPArchComponentFundamentalDomain_isFundamental K hζ b μ).setIntegral_eq hD hf

omit [NormedSpace ℝ E] in
theorem sourceKPArchComponent_integrable_independent
    (D : Set (PGL(2, InfiniteAdeleRing K)))
    (hD : IsFundamentalDomain (sourceKPArchComponentSubgroup K hζ b) D μ)
    (f : PGL(2, InfiniteAdeleRing K) → E)
    (hf : ∀ γ : sourceKPArchComponentSubgroup K hζ b, ∀ g, f (γ • g) = f g) :
    IntegrableOn f (sourceKPArchComponentFundamentalDomain K hζ b μ) μ ↔ IntegrableOn f D μ :=
  (sourceKPArchComponentFundamentalDomain_isFundamental K hζ b μ).integrableOn_iff hD hf

theorem sourceKPArchComponent_integral_unfold (f : PGL(2, InfiniteAdeleRing K) → E)
    (hf : Integrable f μ) :
    ∫ g, f g ∂μ =
      ∑' γ : sourceKPArchComponentSubgroup K hζ b,
        ∫ g in sourceKPArchComponentFundamentalDomain K hζ b μ, f (γ • g) ∂μ :=
  (sourceKPArchComponentFundamentalDomain_isFundamental K hζ b μ).integral_eq_tsum'' f hf

end
end ArtinMatthews
