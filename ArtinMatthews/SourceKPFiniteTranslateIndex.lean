module

public import ArtinMatthews.SourceKPFiniteIntegralIndex
public import Mathlib.GroupTheory.Commensurable
import ArtinMatthews.SourceKPFiniteStabilizerCompact


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite-level cosets for finitely many right translates of the finite cover. -/
namespace ArtinMatthews
open NumberField Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Kf" => sourceKPFiniteLevelSubgroup K hζ
local notation "F" => SourceKPFiniteLevelFiber K hζ
local notation "π" => sourceKPFiniteAdeleProjectiveProjection K hζ

def sourceKPFiniteLevelConjugate (t : Gf) : Subgroup Gf :=
  (Kf).map (MulAut.conj t).toMonoidHom

theorem sourceKPFiniteLevel_orbit_translate_finite (t : Gf) :
    Set.Finite (MulAction.orbit Kf (QuotientGroup.mk t : F)) := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_surjective (π t)
  let S := (fun g : GL (Fin 2) 𝔸ᶠ[K] => g * u) '' (sourceKPFiniteDeepMatrixGroup K : Set _)
  have hS : IsCompact S :=
    (sourceKPFiniteDeepMatrixGroup_isCompact K).image (continuous_mul_const u)
  apply (sourceKPFiniteCover_compact_image_finite K hζ S hS).subset
  rintro x ⟨k, rfl⟩
  refine ⟨k.val * t, ?_, rfl⟩
  obtain ⟨g, hg⟩ := k.prop
  refine ⟨g.val * u, ⟨g.val, g.prop, rfl⟩, ?_⟩
  have hk : π k.val = ProjGenLinGroup.mk g.val := by
    rw [← hg, sourceKPFiniteLevelLift_projection]
  rw [map_mul, map_mul, hk, hu]

theorem sourceKPFiniteLevel_stabilizer_translate (t : Gf) :
    MulAction.stabilizer Kf (QuotientGroup.mk t : F) =
      (sourceKPFiniteLevelConjugate K hζ t).subgroupOf Kf := by
  have h : (QuotientGroup.mk t : Gf ⧸ Kf) =
      t • (QuotientGroup.mk 1 : Gf ⧸ Kf) := by
    change _ = QuotientGroup.mk (t * 1)
    rw [mul_one]
  unfold sourceKPFiniteLevelConjugate
  rw [← MulAction.stabilizer_subgroupOf, h,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulAction.stabilizer_quotient]

theorem sourceKPFiniteLevelConjugate_finiteRelIndex (t : Gf) :
    (sourceKPFiniteLevelConjugate K hζ t).IsFiniteRelIndex Kf := by
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex, ← sourceKPFiniteLevel_stabilizer_translate]
  let q : F := QuotientGroup.mk t
  let : Finite (MulAction.orbit Kf q) := sourceKPFiniteLevel_orbit_translate_finite K hζ t
  exact (Subgroup.finiteIndex_iff_finite_quotient (H := MulAction.stabilizer Kf q)).mpr
    (Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer Kf q))

theorem sourceKPFiniteLevel_commensurable_conjugate (t : Gf) :
    (Kf).Commensurable (sourceKPFiniteLevelConjugate K hζ t) := by
  refine ⟨?_, sourceKPFiniteLevelConjugate_finiteRelIndex K hζ t⟩
  have h := (sourceKPFiniteLevelConjugate_finiteRelIndex K hζ t⁻¹).map
    (MulAut.conj t).toMonoidHom
  have he : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t⁻¹).toMonoidHom =
      MonoidHom.id Gf := by
    ext x
    simp
  rw [sourceKPFiniteLevelConjugate, Subgroup.map_map, he, Subgroup.map_id] at h
  exact h

def sourceKPFiniteTranslateLevel (T : Finset Gf) : Subgroup Gf :=
  Kf ⊓ ⨅ t ∈ T, sourceKPFiniteLevelConjugate K hζ t

theorem sourceKPFiniteTranslateLevel_le (T : Finset Gf) :
    sourceKPFiniteTranslateLevel K hζ T ≤ Kf :=
  inf_le_left

theorem sourceKPFiniteTranslateLevel_le_conjugate (T : Finset Gf) {t : Gf} (ht : t ∈ T) :
    sourceKPFiniteTranslateLevel K hζ T ≤ sourceKPFiniteLevelConjugate K hζ t :=
  inf_le_right.trans ((iInf_le _ t).trans (iInf_le _ ht))

theorem sourceKPFiniteTranslateLevel_finiteRelIndex (T : Finset Gf) :
    (sourceKPFiniteTranslateLevel K hζ T).IsFiniteRelIndex Kf := by
  apply Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr
  have he : (sourceKPFiniteTranslateLevel K hζ T).subgroupOf Kf =
      ⨅ t ∈ T, (sourceKPFiniteLevelConjugate K hζ t).subgroupOf Kf := by
    ext k
    simp only [sourceKPFiniteTranslateLevel, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_iInf, k.prop, true_and]
  rw [he]
  exact Subgroup.finiteIndex_iInf' _ (fun t _ =>
    Subgroup.isFiniteRelIndex_iff_finiteIndex.mp (sourceKPFiniteLevelConjugate_finiteRelIndex K hζ t))

theorem sourceKPFiniteTranslateLevel_finiteRelIndex_conjugate (T : Finset Gf) (t : Gf) :
    (sourceKPFiniteTranslateLevel K hζ T).IsFiniteRelIndex (sourceKPFiniteLevelConjugate K hζ t) :=
  (sourceKPFiniteTranslateLevel_finiteRelIndex K hζ T).trans
    (sourceKPFiniteLevel_commensurable_conjugate K hζ t).1

end
end ArtinMatthews
