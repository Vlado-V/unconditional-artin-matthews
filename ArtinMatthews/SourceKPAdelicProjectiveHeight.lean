module

public import ArtinMatthews.SourceKPAdelicHeightAction
public import ArtinMatthews.SourceKPRationalBruhat


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Iwasawa height on adelic PGL₂ and the cubic cover. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicHeightOnProjective (q : PGL(2, 𝔸[K])) : ℝ :=
  sourceKPAdelicHeight K hζ (Classical.choose (ProjGenLinGroup.mk_surjective q))

theorem sourceKPAdelicHeightOnProjective_mk (g : GL (Fin 2) 𝔸[K]) :
    sourceKPAdelicHeightOnProjective K hζ (ProjGenLinGroup.mk g) = sourceKPAdelicHeight K hζ g :=
  sourceKPAdelicHeight_projective K hζ _ g (Classical.choose_spec (ProjGenLinGroup.mk_surjective _))

theorem sourceKPAdelicHeightOnProjective_pos (q : PGL(2, 𝔸[K])) :
    0 < sourceKPAdelicHeightOnProjective K hζ q := sourceKPAdelicHeight_pos K hζ _

theorem sourceKPAdelicHeightOnProjective_left_rationalBorel (b : PGL(2,K))
    (hb : b ∈ sourceKPRationalBorel K) (q : PGL(2, 𝔸[K])) :
    sourceKPAdelicHeightOnProjective K hζ (ProjGenLinGroup.map (algebraMap K 𝔸[K]) b*q) =
      sourceKPAdelicHeightOnProjective K hζ q := by
  obtain ⟨b,hb,rfl⟩ := hb
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective q
  rw [ProjGenLinGroup.map_mk, ← map_mul, sourceKPAdelicHeightOnProjective_mk,
    sourceKPAdelicHeightOnProjective_mk]
  exact sourceKPAdelicHeight_left_rationalBorel K hζ b hb g

theorem sourceKPAdelicHeightOnProjective_rational_bound (γ : PGL(2,K))
    (g : GL (Fin 2) 𝔸[K]) :
    sourceKPAdelicHeightOnProjective K hζ
      (ProjGenLinGroup.map (algebraMap K 𝔸[K]) γ * ProjGenLinGroup.mk g) ≤
        max (sourceKPAdelicHeight K hζ g) (sourceKPAdelicHeightConstant K hζ g) := by
  obtain ⟨i,hi⟩ := (sourceKPRationalBorelCosetEquiv K).surjective (sourceKPRationalBorelCosetMk K γ)
  rw [sourceKPRationalBorelCosetEquiv_apply] at hi
  have hb := (sourceKPRationalBorelCosetMk_eq_iff K _ _).mp hi
  have he : γ = (γ * (ProjGenLinGroup.mk (sourceKPRationalBruhatMatrix K i))⁻¹) *
      ProjGenLinGroup.mk (sourceKPRationalBruhatMatrix K i) := by group
  rw [he, map_mul, mul_assoc, sourceKPAdelicHeightOnProjective_left_rationalBorel K hζ _ hb]
  cases i with
  | none =>
    simpa only [sourceKPRationalBruhatMatrix, map_one, one_mul,
      sourceKPAdelicHeightOnProjective_mk] using le_max_left
        (sourceKPAdelicHeight K hζ g) (sourceKPAdelicHeightConstant K hζ g)
  | some x =>
    have hm : GeneralLinearGroup.map (algebraMap K 𝔸[K]) (sourceKPRationalBruhatMatrix K (some x)) =
        sourceKPAdelicOpenCellMatrix K x := by
      change GeneralLinearGroup.map (algebraMap K 𝔸[K]) (sourceGL2Weyl * sourceGL2Upper x) = _
      rw [map_mul, ← sourceKPWeylMatrix_field, ← sourceKPUpperMatrix_field,
        sourceKPWeylMatrix_map, sourceKPUpperMatrix_map]
      rfl
    rw [ProjGenLinGroup.map_mk, hm, ← map_mul, sourceKPAdelicHeightOnProjective_mk]
    have hx : (Height.mulHeight₁ x)⁻¹ ^ 2 ≤ 1 := by
      apply pow_le_one₀ (inv_nonneg.mpr (Height.mulHeight₁_pos x).le)
      exact (inv_le_one₀ (Height.mulHeight₁_pos x)).mpr (Height.one_le_mulHeight₁ x)
    exact (sourceKPAdelicHeight_translate K hζ g x).trans
      ((mul_le_of_le_one_right (sourceKPAdelicHeightConstant_pos K hζ g).le hx).trans
        (le_max_right _ _))

def sourceKPAdelicCoverHeight (q : SourceKPAdelicProjective K hζ) : ℝ :=
  sourceKPAdelicHeightOnProjective K hζ (sourceKPAdelicProjectiveProjection K hζ q)

theorem sourceKPAdelicCoverHeight_pos (q : SourceKPAdelicProjective K hζ) :
    0 < sourceKPAdelicCoverHeight K hζ q := sourceKPAdelicHeightOnProjective_pos K hζ _

theorem sourceKPAdelicCoverHeight_right_deep (q : SourceKPAdelicProjective K hζ)
    (k : sourceKPAdelicDeepCompact K hζ) :
    sourceKPAdelicCoverHeight K hζ (q*k.val) = sourceKPAdelicCoverHeight K hζ q := by
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  obtain ⟨k₀,hk₀⟩ := k.property
  unfold sourceKPAdelicCoverHeight
  rw [map_mul, ← hk₀, sourceKPAdelicDeepCompactLift_projection, ← hg, ← map_mul,
    sourceKPAdelicHeightOnProjective_mk, sourceKPAdelicHeightOnProjective_mk]
  exact sourceKPAdelicHeight_right_baseCompact K hζ g k₀.val k₀.property.1

end
end ArtinMatthews
