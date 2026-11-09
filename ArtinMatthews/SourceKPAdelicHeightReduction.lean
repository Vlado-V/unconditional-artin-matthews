module

public import ArtinMatthews.SourceAdelicHeightReduction
public import ArtinMatthews.SourceAdelicDeterminantHeightComparison
public import ArtinMatthews.SourceKPAdelicDeterminantReduction
public import ArtinMatthews.SourceKPAdelicOrbitHeight


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform rational height reduction for the actual GL₂ adelic
group and its cubic projective cover. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicGL2_rational_height_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ g : GL (Fin 2) 𝔸[K], ∃ γ : GL (Fin 2) K,
      c ≤ sourceKPAdelicHeight K hζ (GeneralLinearGroup.map (algebraMap K 𝔸[K]) γ*g) := by
  obtain ⟨c,hc,hshort⟩ := sourceKPAdelicSL2_rational_height_lower K hζ
  obtain ⟨B,hB,hcompare⟩ := sourceKPAdelicHeight_normOne_diagonal_comparison K hζ
  let v₀ : InfinitePlace K := Classical.choice inferInstance
  refine ⟨B⁻¹*c, mul_pos (inv_pos.mpr hB) hc, fun g => ?_⟩
  obtain ⟨q,d,h,hd,he⟩ := sourceKPAdelicSL2_compact_determinant_reduction K hζ v₀ g
  obtain ⟨γ,hγ⟩ := hshort h
  let δ := γ.toGL * sourceKPDiagonalHom K q
  refine ⟨δ, ?_⟩
  have hm : (GeneralLinearGroup.map (algebraMap K 𝔸[K]) δ*g) *
      GeneralLinearGroup.scalar (Fin 2) (sourceKPAdelicDeterminantScale K hζ v₀ g) =
        (GeneralLinearGroup.map (algebraMap K 𝔸[K]) γ.toGL*h.toGL) * sourceKPDiagonalHom 𝔸[K] d := by
    have hh := congrArg (fun a : GL (Fin 2) 𝔸[K] =>
      GeneralLinearGroup.map (algebraMap K 𝔸[K]) γ.toGL*a) he
    simpa only [δ, map_mul, mul_assoc] using hh
  have hp : ProjGenLinGroup.mk (GeneralLinearGroup.map (algebraMap K 𝔸[K]) δ*g) =
      ProjGenLinGroup.mk ((GeneralLinearGroup.map (algebraMap K 𝔸[K]) γ.toGL*h.toGL) *
        sourceKPDiagonalHom 𝔸[K] d) :=
    ProjGenLinGroup.mk_eq_mk_iff.mpr ⟨sourceKPAdelicDeterminantScale K hζ v₀ g,hm⟩
  rw [sourceKPAdelicHeight_projective K hζ _ _ hp]
  exact (mul_le_mul_of_nonneg_left hγ (inv_pos.mpr hB).le).trans (hcompare d hd _).1

theorem sourceKPAdelicCover_rational_height_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ q : SourceKPAdelicProjective K hζ, ∃ γ : PGL(2,K),
      c ≤ sourceKPAdelicCoverHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ*q) := by
  obtain ⟨c,hc,hlower⟩ := sourceKPAdelicGL2_rational_height_lower K hζ
  refine ⟨c,hc,fun q => ?_⟩
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  obtain ⟨γ,hγ⟩ := hlower g
  refine ⟨ProjGenLinGroup.mk γ, ?_⟩
  unfold sourceKPAdelicCoverHeight
  rw [map_mul, sourceKPAdelicProjectiveRationalLift_projection, ProjGenLinGroup.map_mk,
    ← hg, ← map_mul, sourceKPAdelicHeightOnProjective_mk]
  exact hγ

theorem sourceKPAdelicOrbitHeight_uniform_pos :
    ∃ c : ℝ, 0 < c ∧ ∀ q : SourceKPAdelicProjective K hζ,
      c ≤ sourceKPAdelicOrbitHeight K hζ q := by
  obtain ⟨c,hc,hlower⟩ := sourceKPAdelicCover_rational_height_lower K hζ
  refine ⟨c,hc,fun q => ?_⟩
  obtain ⟨γ,hγ⟩ := hlower q
  exact hγ.trans (le_csSup (sourceKPAdelicOrbitHeight_range_bddAbove K hζ q)
    (Set.mem_range_self γ))

end
end ArtinMatthews
