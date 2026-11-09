module

public import ArtinMatthews.IntegerConductor


set_option backward.privateInPublic true
@[expose] public section

/-! The compact open additive subgroup of valuation integers and its actual
surjective residue reduction. -/

namespace ArtinMatthews.QuadraticWeil

open scoped ValuativeRel Classical

noncomputable section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

def integerOpenSubgroup : OpenAddSubgroup K where
  toAddSubgroup := (ValuativeRel.valuation K).integer.toAddSubgroup
  isOpen' := by
    apply AddSubgroup.isOpen_of_mem_nhds
    apply (IsValuativeTopology.mem_nhds_zero_iff _).mpr
    refine ⟨1, ?_⟩
    intro x hx
    change ValuativeRel.valuation K x < 1 at hx
    exact hx.le

theorem integerOpenSubgroup_compact : IsCompact (integerOpenSubgroup K : Set K) :=
  IsNonarchimedeanLocalField.isCompact_closedBall K 1

def integerReduction : integerOpenSubgroup K →+ 𝓀[K] := by
  change 𝒪[K] →+ 𝓀[K]
  exact (IsLocalRing.residue 𝒪[K]).toAddMonoidHom

theorem integerReduction_apply (x : integerOpenSubgroup K) :
    integerReduction K x = IsLocalRing.residue 𝒪[K] ⟨(x : K), x.property⟩ := rfl

theorem integerReduction_surjective : Function.Surjective (integerReduction K) := by
  intro z
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨⟨(x : K), x.property⟩, hx⟩

end

end ArtinMatthews.QuadraticWeil
