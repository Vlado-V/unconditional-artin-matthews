module

public import ArtinMatthews.SourceKPAdelicCuspSeparation


set_option backward.privateInPublic true
@[expose] public section

/-! Separation of the actual high adelic cusp and its rational translates. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicHeight_right_scalar (g : GL (Fin 2) 𝔸[K])
    (u : IdeleGroup (𝓞 K) K) :
    sourceKPAdelicHeight K hζ (g * GeneralLinearGroup.scalar (Fin 2) u) =
      sourceKPAdelicHeight K hζ g := by
  apply sourceKPAdelicHeight_projective K hζ
  rw [map_mul, ProjGenLinGroup.mk_scalar, mul_one]

theorem sourceKPAdelicHeight_rational_borel_separation
    (b : GL (Fin 2) 𝔸[K]) (hb : b ∈ sourceKPRingNormalizedBorel 𝔸[K])
    (γ : GL (Fin 2) K) (hγ : γ 1 0 ≠ 0) :
    sourceKPIdeleAbsoluteNorm K (GeneralLinearGroup.det b) *
      sourceKPAdelicHeight K hζ (GeneralLinearGroup.map (algebraMap K 𝔸[K]) γ * b) ≤ 1 := by
  let c : Kˣ := Units.mk0 (γ 1 0) hγ
  let a := GeneralLinearGroup.det b
  let r := GeneralLinearGroup.map (algebraMap K 𝔸[K]) γ
  let u := IdeleGroup.unitEmbedding (𝓞 K) K c * a
  have ha : (a : 𝔸[K]) = b 0 0 := by
    change Matrix.det (b : Matrix (Fin 2) (Fin 2) 𝔸[K]) = b 0 0
    rw [Matrix.det_fin_two, hb.1, hb.2, mul_one, mul_zero, sub_zero]
  have hrow : (r * b) 1 0 = (u : 𝔸[K]) := by
    change ((r : Matrix (Fin 2) (Fin 2) 𝔸[K]) * b) 1 0 = _
    rw [Matrix.mul_apply, Fin.sum_univ_two, hb.1, mul_zero, add_zero, ← ha]
    rfl
  have hbound := sourceKPAdelicHeight_lowerLeft_bound K hζ (r*b) u hrow
  have hr : sourceKPIdeleAbsoluteNorm K (GeneralLinearGroup.det r) = 1 := by
    dsimp only [r]
    rw [GeneralLinearGroup.map_det]
    change sourceKPIdeleAbsoluteNorm K
      (IdeleGroup.unitEmbedding (𝓞 K) K (GeneralLinearGroup.det γ)) = 1
    exact sourceKPIdeleAbsoluteNorm_principal K _
  have hdet : sourceKPIdeleAbsoluteNorm K (GeneralLinearGroup.det (r*b)) =
      sourceKPIdeleAbsoluteNorm K a := by
    rw [map_mul, map_mul, hr, one_mul]
  have hu : sourceKPIdeleAbsoluteNorm K u = sourceKPIdeleAbsoluteNorm K a := by
    dsimp only [u]
    rw [map_mul, sourceKPIdeleAbsoluteNorm_principal, one_mul]
  have hnorm : sourceKPIdeleAbsoluteNorm K (GeneralLinearGroup.det (r*b) / u^2) =
      (sourceKPIdeleAbsoluteNorm K a)⁻¹ := by
    rw [map_div, map_pow, hdet, hu, pow_two, div_mul_eq_div_div,
      div_self (sourceKPIdeleAbsoluteNorm_pos K a).ne', one_div]
  rw [hnorm] at hbound
  have ha0 := sourceKPIdeleAbsoluteNorm_pos K a
  exact (le_inv_mul_iff₀ ha0).mp (by simpa only [mul_one] using hbound)

theorem sourceKPAdelicHeight_cusp_separation (g : GL (Fin 2) 𝔸[K])
    (γ : GL (Fin 2) K) (hγ : γ 1 0 ≠ 0) :
    sourceKPAdelicHeight K hζ g *
      sourceKPAdelicHeight K hζ (GeneralLinearGroup.map (algebraMap K 𝔸[K]) γ * g) ≤ 1 := by
  let b := sourceKPAdelicIwasawaBorel K hζ g
  let u := sourceKPAdelicIwasawaScalar K hζ g
  let k := sourceKPAdelicIwasawaCompact K hζ g
  have he : GeneralLinearGroup.map (algebraMap K 𝔸[K]) γ * g =
      (GeneralLinearGroup.map (algebraMap K 𝔸[K]) γ * b) *
        GeneralLinearGroup.scalar (Fin 2) u * k := by
    rw [sourceKPAdelicIwasawa_factor K hζ g]
    dsimp only [b, u, k]
    simp only [mul_assoc]
  rw [he, sourceKPAdelicHeight_right_baseCompact K hζ _ k
    (sourceKPAdelicIwasawaCompact_mem K hζ g), sourceKPAdelicHeight_right_scalar]
  exact sourceKPAdelicHeight_rational_borel_separation K hζ b
    (sourceKPAdelicIwasawaBorel_mem K hζ g) γ hγ

theorem sourceKPAdelicHeight_high_overlap (g : GL (Fin 2) 𝔸[K])
    (γ : GL (Fin 2) K) (hg : 1 < sourceKPAdelicHeight K hζ g)
    (hγg : 1 < sourceKPAdelicHeight K hζ
      (GeneralLinearGroup.map (algebraMap K 𝔸[K]) γ * g)) : γ 1 0 = 0 := by
  by_contra hγ
  have h := sourceKPAdelicHeight_cusp_separation K hζ g γ hγ
  have hp := mul_lt_mul_of_pos_left hγg (sourceKPAdelicHeight_pos K hζ g)
  nlinarith

theorem sourceKPAdelicHeightOnProjective_cusp_separation (q : PGL(2, 𝔸[K]))
    (γ : PGL(2, K)) (hγ : γ ∉ sourceKPRationalBorel K) :
    sourceKPAdelicHeightOnProjective K hζ q *
      sourceKPAdelicHeightOnProjective K hζ
        (ProjGenLinGroup.map (algebraMap K 𝔸[K]) γ * q) ≤ 1 := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective q
  obtain ⟨γ, rfl⟩ := ProjGenLinGroup.mk_surjective γ
  have hγ0 : γ 1 0 ≠ 0 := fun h => hγ ((sourceKPRationalBorel_mk_mem_iff K γ).mpr h)
  rw [ProjGenLinGroup.map_mk, ← map_mul, sourceKPAdelicHeightOnProjective_mk,
    sourceKPAdelicHeightOnProjective_mk]
  exact sourceKPAdelicHeight_cusp_separation K hζ g γ hγ0

theorem sourceKPAdelicHeightOnProjective_high_overlap (q : PGL(2, 𝔸[K]))
    (γ : PGL(2, K)) (hq : 1 < sourceKPAdelicHeightOnProjective K hζ q)
    (hγq : 1 < sourceKPAdelicHeightOnProjective K hζ
      (ProjGenLinGroup.map (algebraMap K 𝔸[K]) γ * q)) :
    γ ∈ sourceKPRationalBorel K := by
  by_contra hγ
  have h := sourceKPAdelicHeightOnProjective_cusp_separation K hζ q γ hγ
  have hp := mul_lt_mul_of_pos_left hγq (sourceKPAdelicHeightOnProjective_pos K hζ q)
  nlinarith

theorem sourceKPAdelicCoverHeight_cusp_separation (q : SourceKPAdelicProjective K hζ)
    (γ : PGL(2, K)) (hγ : γ ∉ sourceKPRationalBorel K) :
    sourceKPAdelicCoverHeight K hζ q *
      sourceKPAdelicCoverHeight K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ * q) ≤ 1 := by
  unfold sourceKPAdelicCoverHeight
  rw [map_mul, sourceKPAdelicProjectiveRationalLift_projection]
  exact sourceKPAdelicHeightOnProjective_cusp_separation K hζ _ γ hγ

theorem sourceKPAdelicCoverHeight_high_overlap (q : SourceKPAdelicProjective K hζ)
    (γ : PGL(2, K)) (hq : 1 < sourceKPAdelicCoverHeight K hζ q)
    (hγq : 1 < sourceKPAdelicCoverHeight K hζ
      (sourceKPAdelicProjectiveRationalLift K hζ γ * q)) :
    γ ∈ sourceKPRationalBorel K := by
  apply sourceKPAdelicHeightOnProjective_high_overlap K hζ _ γ hq
  simpa only [sourceKPAdelicCoverHeight, map_mul,
    sourceKPAdelicProjectiveRationalLift_projection] using hγq

theorem sourceKPAdelicHeightOnProjective_high_overlap_iff (q : PGL(2, 𝔸[K]))
    (hq : 1 < sourceKPAdelicHeightOnProjective K hζ q) (γ : PGL(2, K)) :
    1 < sourceKPAdelicHeightOnProjective K hζ
      (ProjGenLinGroup.map (algebraMap K 𝔸[K]) γ * q) ↔ γ ∈ sourceKPRationalBorel K := by
  constructor
  · exact sourceKPAdelicHeightOnProjective_high_overlap K hζ q γ hq
  · intro hγ
    rw [sourceKPAdelicHeightOnProjective_left_rationalBorel K hζ γ hγ]
    exact hq

theorem sourceKPAdelicCoverHeight_high_overlap_iff (q : SourceKPAdelicProjective K hζ)
    (hq : 1 < sourceKPAdelicCoverHeight K hζ q) (γ : PGL(2, K)) :
    1 < sourceKPAdelicCoverHeight K hζ
      (sourceKPAdelicProjectiveRationalLift K hζ γ * q) ↔ γ ∈ sourceKPRationalBorel K := by
  unfold sourceKPAdelicCoverHeight
  rw [map_mul, sourceKPAdelicProjectiveRationalLift_projection]
  exact sourceKPAdelicHeightOnProjective_high_overlap_iff K hζ _ hq γ

end
end ArtinMatthews
