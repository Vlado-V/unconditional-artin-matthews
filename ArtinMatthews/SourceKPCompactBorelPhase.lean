module

public import ArtinMatthews.SourceKPRingBorel
public import ArtinMatthews.SourceKPDeepCubes


set_option backward.privateInPublic true
@[expose] public section

/-! Scalar normalization of a compact triangular matrix in the actual
adelic cubic cover. The wild hypotheses are explicit cube conditions. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPFiniteTwistedMultiplier_normalized_scalar
    (P : HeightOneSpectrum (𝓞 K)) (b : GL (Fin 2) (P.adicCompletion K))
    (hb : b ∈ sourceGL2NormalizedBorel (P.adicCompletion K)) (u : (P.adicCompletion K)ˣ) :
    sourceKPFiniteTwistedMultiplier K hζ P b (GeneralLinearGroup.scalar (Fin 2) u) =
      sourceFiniteKPHilbert K hζ P u (GeneralLinearGroup.det b) := by
  have hprod : (b * GeneralLinearGroup.scalar (Fin 2) u) 1 0 = 0 := by
    rw [sourceKPMatrix_right_scalar_entry, hb.1, zero_mul]
  rw [sourceKPFiniteTwistedMultiplier, sourceKPCochainTwist,
    sourceKPFinitePhase_zero_left K hζ P b hb.1,
    sourceKPFinitePhase_scalar, sourceKPFinitePhase_zero_left K hζ P _ hprod,
    one_mul, one_mul, div_one]
  change sourceKP2Multiplier (sourceFiniteKPHilbert K hζ P) b
    (GeneralLinearGroup.scalar (Fin 2) u) = _
  rw [sourceKP2Multiplier_scalar_right _ (sourceFiniteKPHilbert_diag K hζ P)
    (fun a c => sourceCubicRoot_cube _ (sourceFiniteKPHilbert K hζ P a c)),
    sourceKubotaX_normalizedBorel _ b hb, one_mul]

theorem sourceKPAdeleMultiplier_normalized_scalar
    (b : GL (Fin 2) 𝔸ᶠ[K]) (hb : b ∈ sourceKPRingNormalizedBorel 𝔸ᶠ[K])
    (u : 𝔸ᶠ[K]ˣ)
    (hu : ∀ P, sourceKPFiniteVal K P
      (Units.map (sourceKPAdeleEval K P).toMonoidHom u : P.adicCompletion K) = 1)
    (hbval : ∀ P, sourceKPFiniteVal K P
      (GeneralLinearGroup.det (sourceKPAdeleMatrixAt K P b) : P.adicCompletion K) = 1)
    (huc : ∀ P, (6 : 𝓞 K) ∈ P.asIdeal →
      Units.map (sourceKPAdeleEval K P).toMonoidHom u ∈ sourceKPUnitCubes (P.adicCompletion K)) :
    sourceKPAdeleMultiplier K hζ b (GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
  apply finprod_eq_one_of_forall_eq_one
  intro P
  have hbP : sourceKPAdeleMatrixAt K P b ∈ sourceGL2NormalizedBorel (P.adicCompletion K) := by
    constructor
    · change sourceKPAdeleEval K P (b 1 0) = 0
      rw [hb.1, map_zero]
    · change sourceKPAdeleEval K P (b 1 1) = 1
      rw [hb.2, map_one]
  rw [sourceKPAdeleLocalMultiplier, sourceKPAdeleMatrixAt_scalar,
    sourceKPFiniteTwistedMultiplier_normalized_scalar K hζ P _ hbP]
  have hB : sourceFiniteKPHilbert K hζ P
      (Units.map (sourceKPAdeleEval K P).toMonoidHom u)
      (GeneralLinearGroup.det (sourceKPAdeleMatrixAt K P b)) = 1 := by
    by_cases h6 : (6 : 𝓞 K) ∈ P.asIdeal
    · exact sourceFiniteKPHilbert_of_cube_left K hζ P _ _ (huc P h6)
    · exact sourceFiniteKPHilbert_units K hζ P h6 _ _ (hu P) (hbval P)
  rw [hB, map_one]

theorem sourceKPFiniteAdeleProjectiveLift_normalized_scalar
    (b : GL (Fin 2) 𝔸ᶠ[K]) (hb : b ∈ sourceKPRingNormalizedBorel 𝔸ᶠ[K])
    (u : 𝔸ᶠ[K]ˣ)
    (hu : ∀ P, sourceKPFiniteVal K P
      (Units.map (sourceKPAdeleEval K P).toMonoidHom u : P.adicCompletion K) = 1)
    (hbval : ∀ P, sourceKPFiniteVal K P
      (GeneralLinearGroup.det (sourceKPAdeleMatrixAt K P b) : P.adicCompletion K) = 1)
    (huc : ∀ P, (6 : 𝓞 K) ∈ P.asIdeal →
      Units.map (sourceKPAdeleEval K P).toMonoidHom u ∈ sourceKPUnitCubes (P.adicCompletion K)) :
    sourceKPFiniteAdeleProjectiveLift K hζ (b * GeneralLinearGroup.scalar (Fin 2) u) =
      sourceKPFiniteAdeleProjectiveLift K hζ b := by
  rw [← sourceKPFiniteAdeleProjectiveLift_mul_of_phase_one K hζ b _
    (sourceKPAdeleMultiplier_normalized_scalar K hζ b hb u hu hbval huc),
    sourceKPFiniteAdeleProjectiveLift_scalar, mul_one]

end
end ArtinMatthews
