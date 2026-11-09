module

public import ArtinMatthews.SourceKPCompactCocycle
public import ArtinMatthews.SourceFiniteKPTameUnits
public import ArtinMatthews.SourceFiniteKP2Projective


set_option backward.privateInPublic true
@[expose] public section

/-! The actual tame integral section of the local threefold extension.
The unit and principal-unit laws are derived from the genuine local
CFT symbol and Hensel lifting, so the section takes no splitting premise. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups ValuativeRel Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (h6 : (6 : 𝓞 K) ∉ P.asIdeal)

abbrev SourceFiniteKP2Integral := sourceKPIntegralGroup (sourceKPFiniteVal K P)

def sourceFiniteKP2CompactSection :
    SourceFiniteKP2Integral K P →* SourceFiniteKP2Cover K hζ P where
  toFun g := ⟨sourceKPCompactPhase (sourceKPFiniteVal K P) (sourceFiniteKPHilbert K hζ P) g.val, g.val⟩
  map_one' := by
    apply SourceFiniteKP2Cover.ext
    · exact sourceKPCompactPhase_zero_left (sourceKPFiniteVal K P) (sourceFiniteKPHilbert K hζ P) 1 (by simp)
    · rfl
  map_mul' g h := by
    apply SourceFiniteKP2Cover.ext
    · exact sourceKPCompactPhase_mul (sourceKPFiniteVal K P) (sourceFiniteKPHilbert K hζ P)
        (sourceFiniteKPHilbert_diag K hζ P) (fun a b => sourceCubicRoot_cube _ (sourceFiniteKPHilbert K hζ P a b))
        (sourceFiniteKPHilbert_minus_right K hζ P) (sourceFiniteKPHilbert_steinberg K hζ P)
        (sourceFiniteKPHilbert_units K hζ P h6) (sourceFiniteKPHilbert_principalUnit K hζ P h6)
        g.val h.val g.property h.property
    · rfl

theorem sourceFiniteKP2CompactSection_projection (g : SourceFiniteKP2Integral K P) :
    sourceFiniteKP2Projection K hζ P (sourceFiniteKP2CompactSection K hζ P h6 g) = g.val := rfl

theorem sourceFiniteKP2CompactSection_injective :
    Function.Injective (sourceFiniteKP2CompactSection K hζ P h6) := by
  intro g h he
  exact Subtype.ext (congrArg SourceFiniteKP2Cover.base he)

theorem sourceFiniteKP2CompactSection_upper (x : P.adicCompletion K) (hx : sourceKPFiniteVal K P x ≤ 1) :
    sourceFiniteKP2CompactSection K hζ P h6
        ⟨sourceGL2Upper x, sourceKPIntegralMatrix_upper (sourceKPFiniteVal K P) x hx⟩ =
      sourceFiniteKP2Lift K hζ P (sourceGL2Upper x) := by
  apply SourceFiniteKP2Cover.ext
  · exact sourceKPCompactPhase_zero_left _ _ _ (by simp [sourceGL2Upper])
  · rfl

theorem sourceFiniteKP2CompactSection_diagonal (u : (P.adicCompletion K)ˣ)
    (hu : sourceKPFiniteVal K P (u : P.adicCompletion K) = 1) :
    sourceFiniteKP2CompactSection K hζ P h6
        ⟨sourceGL2Diagonal u, sourceKPIntegralMatrix_diagonal (sourceKPFiniteVal K P) u hu⟩ =
      sourceFiniteKP2Lift K hζ P (sourceGL2Diagonal u) := by
  apply SourceFiniteKP2Cover.ext
  · exact sourceKPCompactPhase_zero_left _ _ _ (by simp [sourceGL2Diagonal])
  · rfl

theorem sourceFiniteKP2CompactSection_weyl :
    sourceFiniteKP2CompactSection K hζ P h6
        ⟨sourceGL2Weyl, sourceKPIntegralMatrix_weyl (sourceKPFiniteVal K P)⟩ =
      sourceFiniteKP2Lift K hζ P sourceGL2Weyl := by
  apply SourceFiniteKP2Cover.ext
  · exact sourceKPCompactPhase_unit_left _ _ _ (by simp [sourceGL2Weyl])
  · rfl

theorem sourceFiniteKP2CompactSection_scalar (u : (P.adicCompletion K)ˣ)
    (hu : sourceKPFiniteVal K P (u : P.adicCompletion K) = 1) :
    sourceFiniteKP2CompactSection K hζ P h6
        ⟨GeneralLinearGroup.scalar (Fin 2) u, sourceKPIntegralMatrix_scalar (sourceKPFiniteVal K P) u hu⟩ =
      sourceFiniteKP2Scalar K hζ P u := by
  apply SourceFiniteKP2Cover.ext
  · exact sourceKPCompactPhase_zero_left _ _ _ (by simp [GeneralLinearGroup.coe_scalar])
  · rfl

end
end ArtinMatthews
