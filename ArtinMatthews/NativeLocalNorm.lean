module

public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanNorm


set_option backward.privateInPublic true
@[expose] public section

/-! The analytic norm is the native local-field norm.  In particular its unit
ball is the valuation ring used by the arithmetic residue construction. -/

namespace ArtinMatthews.QuadraticWeil

open LocalFieldTheory
open scoped ValuativeRel Classical

noncomputable section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem nativeLocalNorm_integer (x : K) :
    letI : NontriviallyNormedField K := localFieldNontriviallyNormedField K
    x ∈ (ValuativeRel.valuation K).integer ↔ ‖x‖ ≤ 1 := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  let : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let : (Valued.v : Valuation K (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField K := localFieldNontriviallyNormedField K
  exact (Valued.toNormedField.norm_le_one_iff (L := K)
    (Γ₀ := ValuativeRel.ValueGroupWithZero K)).symm

theorem nativeLocalNorm_localField :
    letI : NontriviallyNormedField K := localFieldNontriviallyNormedField K
    IsNonarchimedeanLocalField K := by
  let : NontriviallyNormedField K := localFieldNontriviallyNormedField K
  infer_instance

theorem nativeLocalNorm_ultrametric :
    letI : NontriviallyNormedField K := localFieldNontriviallyNormedField K
    IsUltrametricDist K := localFieldIsUltrametricDist K

end

end ArtinMatthews.QuadraticWeil
