module

public import ArtinMatthews.SourceKPAdelicOrbitHeightCompact
public import ArtinMatthews.SourceKPAdelicRationalSum


set_option backward.privateInPublic true
@[expose] public section

/-! Positive height superlevels contain only finitely many rational
Borel cosets, uniformly over compact sets of actual adelic matrices. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCoverHeight_left_rationalBorel (b : PGL(2,K))
    (hb : b ∈ sourceKPRationalBorel K) (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCoverHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ b*q) =
      sourceKPAdelicCoverHeight K hζ q := by
  unfold sourceKPAdelicCoverHeight
  rw [map_mul, sourceKPAdelicProjectiveRationalLift_projection]
  exact sourceKPAdelicHeightOnProjective_left_rationalBorel K hζ b hb _

def sourceKPAdelicRationalHeight (q : SourceKPAdelicProjective K hζ) :
    SourceKPRationalBorelCoset K → ℝ :=
  Quotient.lift (fun a => sourceKPAdelicCoverHeight K hζ
    (sourceKPAdelicProjectiveRationalLift K hζ a*q)) (by
      intro a b h
      have hb : b*a⁻¹ ∈ sourceKPRationalBorel K := QuotientGroup.rightRel_apply.mp h
      have he := sourceKPAdelicCoverHeight_left_rationalBorel K hζ (b*a⁻¹) hb
        (sourceKPAdelicProjectiveRationalLift K hζ a*q)
      simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left] using he.symm)

theorem sourceKPAdelicRationalHeight_mk (q : SourceKPAdelicProjective K hζ)
    (a : PGL(2,K)) :
    sourceKPAdelicRationalHeight K hζ q (sourceKPRationalBorelCosetMk K a) =
      sourceKPAdelicCoverHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ a*q) := rfl

theorem sourceKPAdelicRationalHeight_pos (q : SourceKPAdelicProjective K hζ)
    (c : SourceKPRationalBorelCoset K) : 0 < sourceKPAdelicRationalHeight K hζ q c := by
  induction c using Quotient.inductionOn
  exact sourceKPAdelicCoverHeight_pos K hζ _

theorem sourceKPAdelicRationalHeight_openCell (q : SourceKPAdelicProjective K hζ)
    (g : GL (Fin 2) 𝔸[K])
    (hg : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g) (x : K) :
    sourceKPAdelicRationalHeight K hζ q (sourceKPRationalBorelCosetEquiv K (some x)) =
      sourceKPAdelicHeight K hζ (sourceKPAdelicOpenCellMatrix K x*g) := by
  rw [sourceKPRationalBorelCosetEquiv_apply, sourceKPAdelicRationalHeight_mk]
  unfold sourceKPAdelicCoverHeight
  rw [map_mul, sourceKPAdelicProjectiveRationalLift_projection, ProjGenLinGroup.map_mk, hg]
  have hm : GeneralLinearGroup.map (algebraMap K 𝔸[K])
      (sourceKPRationalBruhatMatrix K (some x)) = sourceKPAdelicOpenCellMatrix K x := by
    change GeneralLinearGroup.map (algebraMap K 𝔸[K]) (sourceGL2Weyl*sourceGL2Upper x) = _
    rw [map_mul, ← sourceKPWeylMatrix_field, ← sourceKPUpperMatrix_field,
      sourceKPWeylMatrix_map, sourceKPUpperMatrix_map]
    rfl
  rw [hm, ← map_mul, sourceKPAdelicHeightOnProjective_mk]

theorem sourceKPAdelicRationalHeight_finite_on_compact
    (S : Set (GL (Fin 2) 𝔸[K])) (hS : IsCompact S) {a : ℝ} (ha : 0 < a) :
    ∃ I : Set (SourceKPRationalBorelCoset K), I.Finite ∧
      ∀ g ∈ S, ∀ q : SourceKPAdelicProjective K hζ,
        sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g →
        ∀ c, a < sourceKPAdelicRationalHeight K hζ q c → c ∈ I := by
  obtain ⟨B,hB,hbound⟩ := sourceKPAdelicHeightConstant_bounded K hζ S hS
  let I : Set (SourceKPRationalBorelCoset K) :=
    sourceKPRationalBorelCosetEquiv K ''
      insert none (some '' {x : K | Height.mulHeight₁ x ≤ B/a})
  have hI : I.Finite :=
    (((NumberField.finite_setOfPred_mulHeight₁_le K (B/a)).image some).insert none).image _
  refine ⟨I,hI,?_⟩
  intro g hg q hq c hc
  obtain ⟨i,rfl⟩ := (sourceKPRationalBorelCosetEquiv K).surjective c
  refine ⟨i,?_,rfl⟩
  cases i with
  | none => exact Set.mem_insert none _
  | some x =>
    apply Set.mem_insert_of_mem
    refine ⟨x,?_,rfl⟩
    rw [sourceKPAdelicRationalHeight_openCell K hζ q g hq x] at hc
    have hx : a < B*(Height.mulHeight₁ x)⁻¹^2 :=
      hc.trans_le ((sourceKPAdelicHeight_translate K hζ g x).trans
        (mul_le_mul_of_nonneg_right (hbound g hg) (sq_nonneg _)))
    have hp := Height.mulHeight₁_pos x
    have hsq : a*(Height.mulHeight₁ x)^2 < B := by
      apply (lt_div_iff₀ (sq_pos_of_pos hp)).mp
      simpa only [div_eq_mul_inv, inv_pow] using hx
    have hlarge : Height.mulHeight₁ x ≤ (Height.mulHeight₁ x)^2 := by
      nlinarith [Height.one_le_mulHeight₁ x]
    apply (le_div_iff₀ ha).mpr
    simpa only [mul_comm] using (mul_le_mul_of_nonneg_left hlarge ha.le).trans hsq.le

theorem sourceKPAdelicRationalHeight_finite (q : SourceKPAdelicProjective K hζ)
    {a : ℝ} (ha : 0 < a) :
    {c : SourceKPRationalBorelCoset K | a < sourceKPAdelicRationalHeight K hζ q c}.Finite := by
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  obtain ⟨I,hI,hbound⟩ := sourceKPAdelicRationalHeight_finite_on_compact K hζ
    {g} (isCompact_singleton) ha
  exact hI.subset (fun c hc => hbound g (Set.mem_singleton g) q hg.symm c hc)

end
end ArtinMatthews
