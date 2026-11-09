module

public import ArtinMatthews.SourceKubotaScalarMultipliers
public import ArtinMatthews.SourceFiniteKPHilbert


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite-place evaluations for every factor in the source's
root, Weyl and Bruhat formulas. The cubic Hilbert character is supplied
by the constructed CFT pairing, not a premise. The global cocycle law
and the automorphic representation remain separate. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

private theorem minusOneUnit_cube (F : Type*) [Field F] :
    sourceMinusOneUnit F ^ 3 = sourceMinusOneUnit F := by
  apply Units.ext
  simp [sourceMinusOneUnit, pow_succ]

theorem sourceFiniteKPHilbert_minus_left (a : (P.adicCompletion K)ˣ) :
    sourceFiniteKPHilbert K hζ P (sourceMinusOneUnit (P.adicCompletion K)) a = 1 := by
  have h := sourceFiniteKPHilbert_cube_left K hζ P (sourceMinusOneUnit (P.adicCompletion K)) a
  rw [minusOneUnit_cube] at h
  exact h

theorem sourceFiniteKPHilbert_minus_right (a : (P.adicCompletion K)ˣ) :
    sourceFiniteKPHilbert K hζ P a (sourceMinusOneUnit (P.adicCompletion K)) = 1 := by
  have h := sourceFiniteKPHilbert_cube_right K hζ P a (sourceMinusOneUnit (P.adicCompletion K))
  rw [minusOneUnit_cube] at h
  exact h

def sourceFiniteKP2Multiplier (g h : GL (Fin 2) (P.adicCompletion K)) :
    rootsOfUnity 3 (P.adicCompletion K) := sourceKP2Multiplier (sourceFiniteKPHilbert K hζ P) g h

theorem sourceFiniteKP2Multiplier_root_diagonal (x : P.adicCompletion K)
    (u : (P.adicCompletion K)ˣ) :
    sourceFiniteKP2Multiplier K hζ P (sourceGL2Upper x) (sourceGL2Diagonal u) = 1 ∧
    sourceFiniteKP2Multiplier K hζ P (sourceGL2Diagonal u) (sourceGL2Upper x) = 1 :=
  ⟨sourceKP2Multiplier_upper_diagonal _ x u, sourceKP2Multiplier_diagonal_upper _ x u⟩

theorem sourceFiniteKP2Multiplier_weyl_diagonal (u : (P.adicCompletion K)ˣ) :
    sourceFiniteKP2Multiplier K hζ P sourceGL2Weyl (sourceGL2Diagonal u) = 1 ∧
    sourceFiniteKP2Multiplier K hζ P (sourceGL2Diagonal u⁻¹) sourceGL2Weyl = 1 ∧
    sourceFiniteKP2Multiplier K hζ P (sourceGL2Diagonal u⁻¹ * sourceGL2Weyl)
      (GeneralLinearGroup.scalar (Fin 2) u) = 1 :=
  ⟨sourceKP2Multiplier_weyl_diagonal _ u (sourceFiniteKPHilbert_diag K hζ P)
      (sourceFiniteKPHilbert_minus_left K hζ P) (sourceFiniteKPHilbert_minus_right K hζ P),
    sourceKP2Multiplier_diagonal_weyl _ u⁻¹ (sourceFiniteKPHilbert_minus_right K hζ P),
    sourceKP2Multiplier_Weyl_scalar _ u (sourceFiniteKPHilbert_diag K hζ P)
      (sourceFiniteKPHilbert_minus_left K hζ P) (sourceFiniteKPHilbert_minus_right K hζ P)⟩

theorem sourceFiniteKP2Multiplier_bruhat (u : (P.adicCompletion K)ˣ) :
    sourceFiniteKP2Multiplier K hζ P sourceGL2Weyl (sourceGL2Upper (u : P.adicCompletion K)) = 1 ∧
    sourceFiniteKP2Multiplier K hζ P (sourceGL2Upper ((u : P.adicCompletion K)⁻¹))
      (sourceBruhatMiddle u) = 1 ∧
    sourceFiniteKP2Multiplier K hζ P
      (sourceGL2Upper ((u : P.adicCompletion K)⁻¹) * sourceBruhatMiddle u)
      (sourceGL2Lower ((u : P.adicCompletion K)⁻¹)) = 1 ∧
    sourceFiniteKP2Multiplier K hζ P (sourceGL2Diagonal (sourceBruhatDiagonal u))
      (GeneralLinearGroup.scalar (Fin 2) u) = 1 :=
  ⟨sourceKP2Multiplier_weyl_upper _ _, sourceKP2Multiplier_upper_middle _ _ u,
    sourceKP2Multiplier_Bruhat_last _ u (sourceFiniteKPHilbert_diag K hζ P)
      (sourceFiniteKPHilbert_minus_right K hζ P),
    sourceKP2Multiplier_Bruhat_scalar _ u (sourceFiniteKPHilbert_diag K hζ P)
      (sourceFiniteKPHilbert_minus_left K hζ P) (sourceFiniteKPHilbert_minus_right K hζ P)⟩

end
end ArtinMatthews
