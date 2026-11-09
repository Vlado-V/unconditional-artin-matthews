module

public import ArtinMatthews.SourceKPProjectiveIwasawa


set_option backward.privateInPublic true
@[expose] public section

/-! The exact canonical lifts used in the spherical Jacquet integral.
The lower root lift is the actual tame compact section for integral
parameters. The Weyl and Bruhat formulas retain the scalar until its
proved disappearance in the projective quotient. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceFiniteKP2ProjectiveLift_mul_of_phase_one (g h : GL (Fin 2) (P.adicCompletion K))
    (hgh : sourceFiniteKP2Multiplier K hζ P g h = 1) :
    sourceFiniteKP2ProjectiveLift K hζ P g * sourceFiniteKP2ProjectiveLift K hζ P h =
      sourceFiniteKP2ProjectiveLift K hζ P (g * h) := by
  rw [sourceFiniteKP2ProjectiveLift_mul, hgh, map_one, one_mul]

theorem sourceFiniteKP2ProjectiveLift_scalar (u : (P.adicCompletion K)ˣ) :
    sourceFiniteKP2ProjectiveLift K hζ P (GeneralLinearGroup.scalar (Fin 2) u) = 1 :=
  sourceFiniteKP2ProjectiveMk_scalar K hζ P u

theorem sourceFiniteKP2ProjectiveLift_upper_diagonal (x : P.adicCompletion K) (u : (P.adicCompletion K)ˣ) :
    sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper x) *
        sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal u) =
      sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal u) *
        sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper (x / (u : P.adicCompletion K))) := by
  rw [sourceFiniteKP2ProjectiveLift_mul_of_phase_one K hζ P _ _
    (sourceFiniteKP2Multiplier_root_diagonal K hζ P x u).1,
    sourceFiniteKP2ProjectiveLift_mul_of_phase_one K hζ P _ _
    (sourceFiniteKP2Multiplier_root_diagonal K hζ P (x / (u : P.adicCompletion K)) u).2,
    sourceGL2Upper_mul_diagonal]

theorem sourceFiniteKP2ProjectiveLift_weyl_diagonal (u : (P.adicCompletion K)ˣ) :
    sourceFiniteKP2ProjectiveLift K hζ P sourceGL2Weyl *
        sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal u) =
      sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal u⁻¹) *
        sourceFiniteKP2ProjectiveLift K hζ P sourceGL2Weyl := by
  have h := sourceFiniteKP2Multiplier_weyl_diagonal K hζ P u
  rw [sourceFiniteKP2ProjectiveLift_mul_of_phase_one K hζ P _ _ h.1,
    sourceFiniteKP2ProjectiveLift_mul_of_phase_one K hζ P _ _ h.2.1,
    sourceGL2Weyl_mul_diagonal,
    ← sourceFiniteKP2ProjectiveLift_mul_of_phase_one K hζ P _ _ h.2.2,
    sourceFiniteKP2ProjectiveLift_scalar, mul_one]

theorem sourceFiniteKP2ProjectiveLift_weyl_upper (u : (P.adicCompletion K)ˣ) :
    sourceFiniteKP2ProjectiveLift K hζ P sourceGL2Weyl *
        sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper (u : P.adicCompletion K)) =
      sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper ((u : P.adicCompletion K)⁻¹)) *
        sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal (sourceBruhatDiagonal u)) *
        sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Lower ((u : P.adicCompletion K)⁻¹)) := by
  have h := sourceFiniteKP2Multiplier_bruhat K hζ P u
  rw [sourceFiniteKP2ProjectiveLift_mul_of_phase_one K hζ P _ _ h.1,
    sourceGL2Weyl_mul_upper_middle,
    ← sourceFiniteKP2ProjectiveLift_mul_of_phase_one K hζ P _ _ h.2.2.1,
    ← sourceFiniteKP2ProjectiveLift_mul_of_phase_one K hζ P _ _ h.2.1,
    sourceBruhatMiddle,
    ← sourceFiniteKP2ProjectiveLift_mul_of_phase_one K hζ P _ _ h.2.2.2,
    sourceFiniteKP2ProjectiveLift_scalar, mul_one]

theorem sourceFiniteKP2ProjectiveCompactSection_lower (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (x : P.adicCompletion K) (hx : sourceKPFiniteVal K P x ≤ 1) :
    sourceFiniteKP2ProjectiveCompactSection K hζ P h6
        ⟨sourceGL2Lower x, sourceKPIntegralMatrix_lower (sourceKPFiniteVal K P) x hx⟩ =
      sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Lower x) := by
  change sourceFiniteKP2ProjectiveMk K hζ P (sourceFiniteKP2CompactSection K hζ P h6 _) =
    sourceFiniteKP2ProjectiveMk K hζ P (sourceFiniteKP2Lift K hζ P _)
  apply congrArg (sourceFiniteKP2ProjectiveMk K hζ P)
  apply SourceFiniteKP2Cover.ext
  · change sourceKPCompactPhase (sourceKPFiniteVal K P) (sourceFiniteKPHilbert K hζ P)
      (sourceGL2Lower x) = 1
    unfold sourceKPCompactPhase
    split_ifs with h
    · have hd : Units.mk0 ((sourceGL2Lower x) 1 1) h.2.2 = 1 := by
        apply Units.ext
        simp [sourceGL2Lower]
      rw [hd, sourceGL2Lower_det, div_one, map_one]
    · rfl
  · rfl

end
end ArtinMatthews
