module

public import ArtinMatthews.LeftQuotientConjugacy
public import ArtinMatthews.SourceKPArchComponentMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! Conjugate arithmetic components have the same quotient measure under
literal left multiplication in the fixed ambient Haar group. -/
namespace ArtinMatthews
open MeasureTheory NumberField Matrix
open scoped NumberField MatrixGroups AdeleRing Classical
noncomputable section

section General
variable {G : Type*} [Group G]

def sourceLeftQuotientConjugacyOfEq (Γ Γ' : Subgroup G) (a : G)
    (hΓ : Γ' = sourceConjugateSubgroup Γ a) :
    Quotient (QuotientGroup.rightRel Γ) ≃ Quotient (QuotientGroup.rightRel Γ') := by
  subst Γ'
  exact sourceLeftQuotientConjugacy Γ a

@[simp] theorem sourceLeftQuotientConjugacyOfEq_mk (Γ Γ' : Subgroup G) (a x : G)
    (hΓ : Γ' = sourceConjugateSubgroup Γ a) :
    sourceLeftQuotientConjugacyOfEq Γ Γ' a hΓ (Quotient.mk _ x) = Quotient.mk _ (a * x) := by
  subst Γ'
  rfl

variable [MeasurableSpace G] [MeasurableMul G]

theorem sourceLeftQuotientConjugacyOfEq_measurable (Γ Γ' : Subgroup G) (a : G)
    (hΓ : Γ' = sourceConjugateSubgroup Γ a) :
    Measurable (sourceLeftQuotientConjugacyOfEq Γ Γ' a hΓ) := by
  subst Γ'
  exact sourceLeftQuotientConjugacy_measurable Γ a

theorem sourceLeftQuotientConjugacyOfEq_measurePreserving
    (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Γ' : Subgroup G) [Countable Γ] (a : G)
    (hΓ : Γ' = sourceConjugateSubgroup Γ a) {F F' : Set G}
    (hF : IsFundamentalDomain Γ F μ) (hF' : IsFundamentalDomain Γ' F' μ) :
    MeasurePreserving (sourceLeftQuotientConjugacyOfEq Γ Γ' a hΓ)
      ((μ.restrict F).map (Quotient.mk (QuotientGroup.rightRel Γ)))
      ((μ.restrict F').map (Quotient.mk (QuotientGroup.rightRel Γ'))) := by
  subst Γ'
  exact sourceLeftQuotientConjugacy_measurePreserving μ Γ a hF hF'

end General

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (b c : SourceKPFiniteLevelFiber K hζ)
    (a : PGL(2, InfiniteAdeleRing K))
    (hΓ : sourceKPArchComponentSubgroup K hζ c =
      sourceConjugateSubgroup (sourceKPArchComponentSubgroup K hζ b) a)

def sourceKPArchComponentConjugacy :
    SourceKPArchComponentQuotient K hζ b ≃ SourceKPArchComponentQuotient K hζ c :=
  sourceLeftQuotientConjugacyOfEq (sourceKPArchComponentSubgroup K hζ b)
    (sourceKPArchComponentSubgroup K hζ c) a hΓ

@[simp] theorem sourceKPArchComponentConjugacy_mk (g : PGL(2, InfiniteAdeleRing K)) :
    sourceKPArchComponentConjugacy K hζ b c a hΓ (sourceKPArchComponentQuotientMap K hζ b g) =
      sourceKPArchComponentQuotientMap K hζ c (a * g) :=
  sourceLeftQuotientConjugacyOfEq_mk _ _ _ _ _

theorem sourceKPArchComponentConjugacy_measurable :
    Measurable (sourceKPArchComponentConjugacy K hζ b c a hΓ) :=
  sourceLeftQuotientConjugacyOfEq_measurable _ _ _ _

theorem sourceKPArchComponentConjugacy_measurePreserving
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) [μ.IsMulLeftInvariant] :
    MeasurePreserving (sourceKPArchComponentConjugacy K hζ b c a hΓ)
      (sourceKPArchComponentQuotientMeasure K hζ b μ)
      (sourceKPArchComponentQuotientMeasure K hζ c μ) :=
  sourceLeftQuotientConjugacyOfEq_measurePreserving μ _ _ _ _
    (sourceKPArchComponentFundamentalDomain_isFundamental K hζ b μ)
    (sourceKPArchComponentFundamentalDomain_isFundamental K hζ c μ)

end
end ArtinMatthews
