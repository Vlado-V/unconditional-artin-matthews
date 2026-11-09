module

public import ArtinMatthews.SourceKPFiniteLevel
public import Mathlib.Topology.Algebra.OpenSubgroup


set_option backward.privateInPublic true
@[expose] public section

/-! Finitely many finite-level cover cosets above a compact matrix set. -/

namespace ArtinMatthews
open NumberField Topology Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K]

def sourceKPFiniteIntegralDeepSubgroup : Subgroup (sourceKPFiniteIntegralMatrixGroup K) :=
  (sourceKPFiniteDeepMatrixGroup K).comap (sourceKPFiniteIntegralMatrixGroup K).subtype

abbrev SourceKPFiniteIntegralMatrixCoset :=
  sourceKPFiniteIntegralMatrixGroup K ⧸ sourceKPFiniteIntegralDeepSubgroup K

instance sourceKPFiniteIntegralMatrixCoset_finite :
    Finite (SourceKPFiniteIntegralMatrixCoset K) := by
  let : CompactSpace (sourceKPFiniteIntegralMatrixGroup K) :=
    isCompact_iff_compactSpace.mp (sourceKPFiniteIntegralMatrixGroup_isCompact K)
  exact Subgroup.quotient_finite_of_isOpen _
    ((sourceKPFiniteDeepMatrixGroup_isOpen K).preimage continuous_subtype_val)

abbrev SourceKPFiniteMatrixLevel :=
  GL (Fin 2) 𝔸ᶠ[K] ⧸ sourceKPFiniteDeepMatrixGroup K

theorem sourceKPFiniteMatrixLevel_compact_image_finite
    (S : Set (GL (Fin 2) 𝔸ᶠ[K])) (hS : IsCompact S) :
    Set.Finite ((QuotientGroup.mk : GL (Fin 2) 𝔸ᶠ[K] → SourceKPFiniteMatrixLevel K) '' S) := by
  let : DiscreteTopology (SourceKPFiniteMatrixLevel K) :=
    QuotientGroup.discreteTopology (sourceKPFiniteDeepMatrixGroup_isOpen K)
  exact (hS.image QuotientGroup.continuous_mk).finite_of_discrete

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPFiniteIntegralCoverGroup : Subgroup (SourceKPFiniteAdeleProjective K hζ) :=
  ((sourceKPFiniteIntegralMatrixGroup K).map ProjGenLinGroup.mk).comap
    (sourceKPFiniteAdeleProjectiveProjection K hζ)

theorem sourceKPFiniteIntegralCoverGroup_mem (g : SourceKPFiniteAdeleProjective K hζ) :
    g ∈ sourceKPFiniteIntegralCoverGroup K hζ ↔
      ∃ r : sourceKPFiniteIntegralMatrixGroup K,
        ProjGenLinGroup.mk r.val = sourceKPFiniteAdeleProjectiveProjection K hζ g := by
  constructor
  · rintro ⟨r, hr, he⟩
    exact ⟨⟨r, hr⟩, he⟩
  · rintro ⟨r, he⟩
    exact ⟨r.val, r.property, he⟩

theorem sourceKPFiniteLevelLift_eq (k : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPFiniteLevelLift K hζ k = sourceKPFiniteAdeleProjectiveLift K hζ k.val := by
  change (sourceKPFiniteDeepCoverLift K hζ k).2 = _
  rw [sourceKPFiniteDeepCoverLift_eq]
  change sourceKPFiniteAdeleProjectiveLift K hζ
    ((sourceKPGL2ProductEquiv K (sourceKPFiniteMatrixEmbedding K k.val)).2) = _
  rw [sourceKPFiniteMatrixEmbedding_product]

theorem sourceKPFiniteLevelLift_projection (k : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPFiniteAdeleProjectiveProjection K hζ (sourceKPFiniteLevelLift K hζ k) =
      ProjGenLinGroup.mk k.val := by
  rw [sourceKPFiniteLevelLift_eq]
  rfl

theorem sourceKPFiniteLevelSubgroup_le_integralCover :
    sourceKPFiniteLevelSubgroup K hζ ≤ sourceKPFiniteIntegralCoverGroup K hζ := by
  rintro g ⟨k, rfl⟩
  apply (sourceKPFiniteIntegralCoverGroup_mem K hζ _).mpr
  exact ⟨⟨k.val, k.property.1⟩, (sourceKPFiniteLevelLift_projection K hζ k).symm⟩

theorem sourceKPFiniteCover_level_decomposition
    (g : SourceKPFiniteAdeleProjective K hζ) (r : GL (Fin 2) 𝔸ᶠ[K])
    (hr : ProjGenLinGroup.mk r = sourceKPFiniteAdeleProjectiveProjection K hζ g) :
    ∃ z : rootsOfUnity 3 K, ∃ k : sourceKPFiniteDeepMatrixGroup K,
        g = (sourceKPFiniteAdeleProjectiveCenter K hζ z *
          sourceKPFiniteAdeleProjectiveLift K hζ
            (QuotientGroup.mk r : SourceKPFiniteMatrixLevel K).out) *
              sourceKPFiniteLevelLift K hζ k := by
  let q : SourceKPFiniteMatrixLevel K := QuotientGroup.mk r
  have hk : q.out⁻¹ * r ∈ sourceKPFiniteDeepMatrixGroup K :=
    QuotientGroup.eq.mp (Quotient.out_eq' q)
  let k : sourceKPFiniteDeepMatrixGroup K := ⟨q.out⁻¹ * r, hk⟩
  let p := sourceKPFiniteAdeleProjectiveLift K hζ q.out * sourceKPFiniteLevelLift K hζ k
  have hp : sourceKPFiniteAdeleProjectiveProjection K hζ p =
      sourceKPFiniteAdeleProjectiveProjection K hζ g := by
    change sourceKPFiniteAdeleProjectiveProjection K hζ
      (sourceKPFiniteAdeleProjectiveLift K hζ q.out * sourceKPFiniteLevelLift K hζ k) = _
    rw [map_mul, sourceKPFiniteLevelLift_projection]
    change ProjGenLinGroup.mk q.out * ProjGenLinGroup.mk (q.out⁻¹ * r) = _
    rw [← map_mul, mul_inv_cancel_left]
    exact hr
  have hkernel : g * p⁻¹ ∈ (sourceKPFiniteAdeleProjectiveProjection K hζ).ker := by
    change sourceKPFiniteAdeleProjectiveProjection K hζ (g * p⁻¹) = 1
    rw [map_mul, map_inv, hp, mul_inv_cancel]
  rw [← sourceKPFiniteAdeleProjective_exact K hζ] at hkernel
  obtain ⟨z, hz⟩ := hkernel
  refine ⟨z, k, ?_⟩
  calc
    g = sourceKPFiniteAdeleProjectiveCenter K hζ z * p :=
      (eq_mul_inv_iff_mul_eq.mp hz).symm
    _ = _ := (mul_assoc _ _ _).symm

theorem sourceKPFiniteCover_compact_image_finite
    (S : Set (GL (Fin 2) 𝔸ᶠ[K])) (hS : IsCompact S) :
    Set.Finite ((QuotientGroup.mk : SourceKPFiniteAdeleProjective K hζ →
      SourceKPFiniteLevelFiber K hζ) ''
        ((sourceKPFiniteAdeleProjectiveProjection K hζ) ⁻¹' (ProjGenLinGroup.mk '' S))) := by
  let Q := (QuotientGroup.mk : GL (Fin 2) 𝔸ᶠ[K] → SourceKPFiniteMatrixLevel K) '' S
  have hQ : Q.Finite := sourceKPFiniteMatrixLevel_compact_image_finite K S hS
  let : Finite Q := hQ
  let f : rootsOfUnity 3 K × Q → SourceKPFiniteLevelFiber K hζ := fun p =>
    QuotientGroup.mk (sourceKPFiniteAdeleProjectiveCenter K hζ p.1 *
      sourceKPFiniteAdeleProjectiveLift K hζ p.2.val.out)
  apply (Set.finite_range f).subset
  rintro x ⟨g, hg, rfl⟩
  obtain ⟨r, hrS, hr⟩ := hg
  obtain ⟨z, k, hg⟩ := sourceKPFiniteCover_level_decomposition K hζ g r hr
  refine ⟨(z, ⟨QuotientGroup.mk r, ⟨r, hrS, rfl⟩⟩), ?_⟩
  change QuotientGroup.mk (sourceKPFiniteAdeleProjectiveCenter K hζ z *
    sourceKPFiniteAdeleProjectiveLift K hζ
      (QuotientGroup.mk r : SourceKPFiniteMatrixLevel K).out) = QuotientGroup.mk g
  rw [hg]
  exact (QuotientGroup.mk_mul_of_mem (s := sourceKPFiniteLevelSubgroup K hζ) _ ⟨k, rfl⟩).symm

theorem sourceKPFiniteIntegralCover_image_finite :
    Set.Finite ((QuotientGroup.mk : SourceKPFiniteAdeleProjective K hζ →
      SourceKPFiniteLevelFiber K hζ) '' (sourceKPFiniteIntegralCoverGroup K hζ : Set _)) :=
  sourceKPFiniteCover_compact_image_finite K hζ _ (sourceKPFiniteIntegralMatrixGroup_isCompact K)

end
end ArtinMatthews
