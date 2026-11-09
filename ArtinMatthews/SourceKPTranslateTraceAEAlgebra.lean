module

public import ArtinMatthews.SourceKPTranslateGramCompactAE


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite trace is linear and independent of null changes in a
common-level representative. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Filter
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "FJ" => SourceKPTranslateFiniteLevelFiber K hζ T
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ T
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "μJ" => sourceKPTranslateCompactHaar K hζ T
local notation "q" => sourceKPFiniteLevelToCompact K hζ
local notation "qJ" => sourceKPTranslateRepresentativeToCompact K hζ T
local notation "H" => SourceKPGenuineAutomorphicL2 K hζ
local notation "Tr[" t ", " ht "]" => sourceKPTranslateCompactTrace K hζ T t ht

def sourceKPTranslateCompactTraceLinear (t : Gf) (ht : J ≤ D t) :
    (YJ → ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun := Tr[t, ht]
  map_add' v w := by
    funext y
    obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
    simp only [sourceKPTranslateCompactTrace_upper, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a v := by
    funext y
    obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
    simp only [sourceKPTranslateCompactTrace_upper, Pi.smul_apply, Finset.smul_sum,
      RingHom.id_apply]

theorem sourceKPTranslateCompactTraceLinear_apply (t : Gf) (ht : J ≤ D t) (v : YJ → ℂ) :
    sourceKPTranslateCompactTraceLinear K hζ T t ht v = Tr[t, ht] v :=
  rfl

theorem sourceKPTranslateCompactTrace_congr_ae {M : Type*} [AddCommMonoid M]
    (t : Gf) (ht : J ≤ D t) {v w : YJ → M} (h : v =ᵐ[μJ] w) :
    Tr[t, ht] v =ᵐ[μY] Tr[t, ht] w := by
  apply sourceKPFiniteLevelToCompact_ae_of_comp K hζ
  have h' := (sourceKPTranslateRepresentativeToCompact_full_quasiMeasurePreserving K hζ T).ae h
  have hall := sourceKPTranslateRepresentative_ae_forall_coset K hζ T _ h'
  filter_upwards [hall] with x hx
  let p := sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk x.1)
  change Tr[t, ht] v (q x) = Tr[t, ht] w (q x)
  rw [show q x = sourceKPUpperToCompact K hζ x.2 p from
    (sourceKPUpperToCompact_mk K hζ x.2 x.1).symm,
    sourceKPTranslateCompactTrace_upper, sourceKPTranslateCompactTrace_upper]
  exact Finset.sum_congr rfl (fun c _ => hx c.val)

theorem sourceKPTranslateGenuineGramL2_trace_pullback_ae (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (g : H) :
    ((sourceKPTranslateGenuineGramL2 K hζ T t ht u hu g).val : Y → ℂ) =ᵐ[μY]
      Tr[t, ht] (sourceKPTranslateGenuinePullbackL2 K hζ T u hu g : YJ → ℂ) :=
  (sourceKPTranslateGenuineGramL2_trace_ae K hζ T t ht u hu g).trans
    (sourceKPTranslateCompactTrace_congr_ae K hζ T t ht
      (sourceKPTranslateCompactPullbackL2_coe K hζ T u hu g.val).symm)

end
end ArtinMatthews
