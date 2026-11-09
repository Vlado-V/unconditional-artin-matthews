module

public import ArtinMatthews.SourceKPProjectiveIwasawa
public import ArtinMatthews.SourceKPTameBorelRepresentation


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact/Borel intersection fixes the spherical value.
An integral scalar removes the bottom-right entry in the compact
representative. Its proved scalar lift introduces no central phase. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (h6 : (6 : 𝓞 K) ∉ P.asIdeal)

theorem sourceFiniteKPProjectiveBorel_compact_lift (b : SourceFiniteKPProjectiveBorel K hζ P)
    (k : SourceFiniteKP2Integral K P) (hbk : b.val = sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k) :
    ∃ (g : GL (Fin 2) (P.adicCompletion K)) (hg : g ∈ sourceGL2NormalizedBorel (P.adicCompletion K)),
      sourceKPFiniteVal K P (GeneralLinearGroup.det g : P.adicCompletion K) = 1 ∧
      b = sourceFiniteKPProjectiveBorelEquiv K hζ P (sourceFiniteKPNormalizedBorelLift K hζ P g hg) := by
  let E := sourceFiniteKPProjectiveBorelEquiv K hζ P
  let x := E.symm b
  let s := sourceFiniteKP2CompactSection K hζ P h6
  let ν := sourceKPFiniteVal K P
  have hx : E x = b := E.apply_symm_apply b
  have hp : sourceFiniteKP2ProjectiveMk K hζ P x.val = sourceFiniteKP2ProjectiveMk K hζ P (s k) := by
    rw [← sourceFiniteKPProjectiveBorelEquiv_val]
    change (E x).val = sourceFiniteKP2ProjectiveMk K hζ P (s k)
    rw [hx]
    exact hbk
  obtain ⟨y, ⟨u, rfl⟩, hu⟩ := (QuotientGroup.mk'_eq_mk' _).mp hp
  have hb := sourceFiniteKPNormalizedBorel_bottom K hζ P x
  have he : x.val.base * GeneralLinearGroup.scalar (Fin 2) u = k.val :=
    congrArg SourceFiniteKP2Cover.base hu
  have h10 : k.val 1 0 = 0 := by
    rw [← he, sourceGL2_right_scalar_apply, hb.1, zero_mul]
  have h11 : k.val 1 1 = (u : P.adicCompletion K) := by
    rw [← he, sourceGL2_right_scalar_apply, hb.2, one_mul]
  have hv : ν (u : P.adicCompletion K) = 1 := by
    rw [← h11]
    refine (sourceKPIntegralMatrix_bottom_unit ν k.property).resolve_left ?_
    rw [h10, map_zero]
    exact zero_ne_one
  let ku : SourceFiniteKP2Integral K P :=
    ⟨GeneralLinearGroup.scalar (Fin 2) u, sourceKPIntegralMatrix_scalar ν u hv⟩
  let k₀ := k * ku⁻¹
  have hs : s ku = sourceFiniteKP2Scalar K hζ P u :=
    sourceFiniteKP2CompactSection_scalar K hζ P h6 u hv
  have hk₀ : s k₀ = x.val := by
    change s (k * ku⁻¹) = x.val
    rw [map_mul, map_inv, hs, ← hu, mul_inv_cancel_right]
  have hg : k₀.val = x.val.base := congrArg SourceFiniteKP2Cover.base hk₀
  have hd := k₀.property.det_unit
  rw [hg] at hd
  have hz : x.val.central = 1 := by
    rw [← hk₀]
    exact sourceKPCompactPhase_zero_left ν (sourceFiniteKPHilbert K hζ P) k₀.val
      (by rw [hg, hb.1])
  refine ⟨x.val.base, x.property, hd, ?_⟩
  rw [← hx]
  apply congrArg E
  apply Subtype.ext
  apply SourceFiniteKP2Cover.ext
  · exact hz
  · rfl

variable (π : (P.adicCompletion K)ˣ)
    (hπ : sourceKPFiniteVal K P (π : P.adicCompletion K) = WithZero.exp (-1 : ℤ))

theorem sourceKPTameBorelRepresentation_compact_fixed (b : SourceFiniteKPProjectiveBorel K hζ P)
    (k : SourceFiniteKP2ProjectiveCompact K hζ P h6) (hbk : b.val = k.val) :
    sourceKPTameBorelRepresentation K hζ P h6 π hπ b (sourceJacquetBasis 0) = sourceJacquetBasis 0 := by
  obtain ⟨k₀, hk₀⟩ := k.property
  obtain ⟨g, hg, hd, he⟩ := sourceFiniteKPProjectiveBorel_compact_lift K hζ P h6 b k₀ (hbk.trans hk₀.symm)
  rw [he, sourceKPTameBorelRepresentation_of_normalized]
  exact sourceKPTameNormalizedBorelRepresentation_lift_unit K hζ P h6 π hπ g hg hd

end
end ArtinMatthews
