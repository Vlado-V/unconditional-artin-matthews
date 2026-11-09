module

public import ArtinMatthews.SourceKPAdeleWeylCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! The exact lifted Weyl conjugation in the actual finite adelic
projective cover. The scalar in the matrix formula dies in the
proved projective quotient, with no remaining cubic phase. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdeleMatrixAt_weyl (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPAdeleMatrixAt K P (sourceKPWeylMatrix 𝔸ᶠ[K]) = sourceGL2Weyl :=
  (sourceKPWeylMatrix_map (sourceKPAdeleEval K P)).trans (sourceKPWeylMatrix_field _)

theorem sourceKPAdeleMatrixAt_diagonal (P : HeightOneSpectrum (𝓞 K)) (x : 𝔸ᶠ[K]ˣ) :
    sourceKPAdeleMatrixAt K P (sourceKPDiagonalHom 𝔸ᶠ[K] x) =
      sourceGL2Diagonal (Units.map (sourceKPAdeleEval K P).toMonoidHom x) :=
  (sourceKPDiagonalHom_map (sourceKPAdeleEval K P) x).trans (sourceKPDiagonalHom_field _)

theorem sourceKPAdeleMultiplier_weyl_diagonal (u : 𝔸ᶠ[K]ˣ) :
    sourceKPAdeleMultiplier K hζ (sourceKPWeylMatrix 𝔸ᶠ[K]) (sourceKPDiagonalHom 𝔸ᶠ[K] u) = 1 ∧
      sourceKPAdeleMultiplier K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] u⁻¹) (sourceKPWeylMatrix 𝔸ᶠ[K]) = 1 ∧
      sourceKPAdeleMultiplier K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] u⁻¹ * sourceKPWeylMatrix 𝔸ᶠ[K])
        (GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
  have hP (P : HeightOneSpectrum (𝓞 K)) :
      sourceKPAdeleLocalMultiplier K hζ (sourceKPWeylMatrix 𝔸ᶠ[K]) (sourceKPDiagonalHom 𝔸ᶠ[K] u) P = 1 ∧
      sourceKPAdeleLocalMultiplier K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] u⁻¹) (sourceKPWeylMatrix 𝔸ᶠ[K]) P = 1 ∧
      sourceKPAdeleLocalMultiplier K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] u⁻¹ * sourceKPWeylMatrix 𝔸ᶠ[K])
        (GeneralLinearGroup.scalar (Fin 2) u) P = 1 := by
    let v := Units.map (sourceKPAdeleEval K P).toMonoidHom
    have h := sourceKPFiniteTwistedMultiplier_weyl_diagonal K hζ P (v u)
    refine ⟨?_, ?_, ?_⟩
    · rw [sourceKPAdeleLocalMultiplier, sourceKPAdeleMatrixAt_weyl, sourceKPAdeleMatrixAt_diagonal, h.1, map_one]
    · rw [sourceKPAdeleLocalMultiplier, sourceKPAdeleMatrixAt_diagonal, sourceKPAdeleMatrixAt_weyl,
        map_inv (Units.map (sourceKPAdeleEval K P).toMonoidHom), h.2.1, map_one]
    · rw [sourceKPAdeleLocalMultiplier, map_mul (sourceKPAdeleMatrixAt K P), sourceKPAdeleMatrixAt_diagonal,
        sourceKPAdeleMatrixAt_weyl, sourceKPAdeleMatrixAt_scalar,
        map_inv (Units.map (sourceKPAdeleEval K P).toMonoidHom), h.2.2, map_one]
  exact ⟨finprod_eq_one_of_forall_eq_one (fun P => (hP P).1),
    finprod_eq_one_of_forall_eq_one (fun P => (hP P).2.1),
    finprod_eq_one_of_forall_eq_one (fun P => (hP P).2.2)⟩

def sourceKPFiniteAdeleProjectiveLift (g : GL (Fin 2) 𝔸ᶠ[K]) : SourceKPFiniteAdeleProjective K hζ :=
  sourceKPFiniteAdeleProjectiveMk K hζ ⟨1, g⟩

theorem sourceKPFiniteAdeleProjectiveLift_mul_of_phase_one (g h : GL (Fin 2) 𝔸ᶠ[K])
    (hgh : sourceKPAdeleMultiplier K hζ g h = 1) :
    sourceKPFiniteAdeleProjectiveLift K hζ g * sourceKPFiniteAdeleProjectiveLift K hζ h =
      sourceKPFiniteAdeleProjectiveLift K hζ (g * h) := by
  unfold sourceKPFiniteAdeleProjectiveLift
  rw [← map_mul]
  apply congrArg (sourceKPFiniteAdeleProjectiveMk K hζ)
  apply SourceKPFiniteAdeleCover.ext
  · change 1 * 1 * sourceKPAdeleMultiplier K hζ g h = 1
    rw [hgh, mul_one, mul_one]
  · rfl

theorem sourceKPFiniteAdeleProjectiveLift_scalar (u : 𝔸ᶠ[K]ˣ) :
    sourceKPFiniteAdeleProjectiveLift K hζ (GeneralLinearGroup.scalar (Fin 2) u) = 1 :=
  sourceKPFiniteAdeleProjectiveMk_scalar K hζ u

theorem sourceKPFiniteAdeleProjectiveLift_weyl_diagonal (u : 𝔸ᶠ[K]ˣ) :
    sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPWeylMatrix 𝔸ᶠ[K]) * sourceKPFiniteAdeleProjectiveDiagonalLift K hζ u =
      sourceKPFiniteAdeleProjectiveDiagonalLift K hζ u⁻¹ * sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPWeylMatrix 𝔸ᶠ[K]) := by
  have h := sourceKPAdeleMultiplier_weyl_diagonal K hζ u
  change sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPWeylMatrix 𝔸ᶠ[K]) *
      sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] u) =
    sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] u⁻¹) *
      sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPWeylMatrix 𝔸ᶠ[K])
  rw [sourceKPFiniteAdeleProjectiveLift_mul_of_phase_one K hζ _ _ h.1,
    sourceKPFiniteAdeleProjectiveLift_mul_of_phase_one K hζ _ _ h.2.1,
    sourceKPWeylMatrix_mul_diagonal,
    ← sourceKPFiniteAdeleProjectiveLift_mul_of_phase_one K hζ _ _ h.2.2,
    sourceKPFiniteAdeleProjectiveLift_scalar, mul_one]

theorem sourceKPFiniteAdeleProjectiveRationalLift_weyl :
    sourceKPFiniteAdeleProjectiveRationalLift K hζ (ProjGenLinGroup.mk (sourceKPWeylMatrix K)) =
      sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPWeylMatrix 𝔸ᶠ[K]) := by
  have hphase : ∏ᶠ P, sourceKPRationalLocalPhase K hζ (sourceKPWeylMatrix K) P = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro P
    rw [sourceKPRationalLocalPhase, sourceKPAdeleMatrixAt_rational, sourceKPWeylMatrix_map,
      sourceKPWeylMatrix_field, sourceKPFinitePhase_weyl, map_one]
  have hbase : sourceKPRationalDiagonal K (sourceKPWeylMatrix K) = sourceKPWeylMatrix 𝔸ᶠ[K] :=
    sourceKPWeylMatrix_map (algebraMap K 𝔸ᶠ[K])
  rw [sourceKPFiniteAdeleProjectiveRationalLift_mk, hphase, inv_one, hbase]
  rfl

end
end ArtinMatthews
