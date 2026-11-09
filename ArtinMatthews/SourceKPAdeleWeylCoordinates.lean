module

public import ArtinMatthews.SourceKPFiniteAdeleTorus


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Weyl matrix over the adele ring and the exact local
cochain values needed to conjugate the normalized torus. The
three products in the lifted Weyl identity all have phase one. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups Classical
noncomputable section

def sourceKPWeylMatrix (R : Type*) [CommRing R] : GL (Fin 2) R :=
  GeneralLinearGroup.mk'' !![0, 1; 1, 0] (by simp [Matrix.det_fin_two])

theorem sourceKPWeylMatrix_field (F : Type*) [Field F] : sourceKPWeylMatrix F = (sourceGL2Weyl : GL (Fin 2) F) := by
  apply Units.ext
  rfl

theorem sourceKPWeylMatrix_map {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T) :
    GeneralLinearGroup.map f (sourceKPWeylMatrix R) = sourceKPWeylMatrix T := by
  apply GeneralLinearGroup.ext
  intro i j
  change f ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R) i j) =
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) T) i j
  fin_cases i <;> fin_cases j <;> simp

theorem sourceKPWeylMatrix_square (R : Type*) [CommRing R] :
    sourceKPWeylMatrix R * sourceKPWeylMatrix R = 1 := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceKPWeylMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem sourceKPWeylMatrix_mul_diagonal {R : Type*} [CommRing R] (u : Rˣ) :
    sourceKPWeylMatrix R * sourceKPDiagonalHom R u =
      sourceKPDiagonalHom R u⁻¹ * sourceKPWeylMatrix R * GeneralLinearGroup.scalar (Fin 2) u := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceKPWeylMatrix, sourceKPDiagonalHom, Matrix.mul_apply, Fin.sum_univ_two,
      GeneralLinearGroup.coe_scalar, Matrix.diagonal_apply]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceKPFinitePhase_zero_right (g : GL (Fin 2) (P.adicCompletion K)) (hg : g 1 1 = 0) :
    sourceKPFinitePhase K hζ P g = 1 := by
  by_cases h6 : (6 : 𝓞 K) ∉ P.asIdeal
  · rw [sourceKPFinitePhase, ite_eq_left h6, sourceKPCompactPhase]
    simp [hg]
  · rw [sourceKPFinitePhase, ite_eq_right h6]

theorem sourceKPFinitePhase_weyl : sourceKPFinitePhase K hζ P sourceGL2Weyl = 1 :=
  sourceKPFinitePhase_zero_right K hζ P _ (by simp [sourceGL2Weyl])

private theorem sourceKPFiniteTwistedMultiplier_eq_of_phase_one (g h : GL (Fin 2) (P.adicCompletion K))
    (hg : sourceKPFinitePhase K hζ P g = 1) (hh : sourceKPFinitePhase K hζ P h = 1)
    (hgh : sourceKPFinitePhase K hζ P (g * h) = 1) :
    sourceKPFiniteTwistedMultiplier K hζ P g h = sourceFiniteKP2Multiplier K hζ P g h := by
  rw [sourceKPFiniteTwistedMultiplier, sourceKPCochainTwist, hg, hh, hgh, one_mul, one_mul, div_one]

theorem sourceKPFiniteTwistedMultiplier_weyl_diagonal (u : (P.adicCompletion K)ˣ) :
    sourceKPFiniteTwistedMultiplier K hζ P sourceGL2Weyl (sourceGL2Diagonal u) = 1 ∧
      sourceKPFiniteTwistedMultiplier K hζ P (sourceGL2Diagonal u⁻¹) sourceGL2Weyl = 1 ∧
      sourceKPFiniteTwistedMultiplier K hζ P (sourceGL2Diagonal u⁻¹ * sourceGL2Weyl)
        (GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
  have hWD : sourceKPFinitePhase K hζ P (sourceGL2Weyl * sourceGL2Diagonal u) = 1 :=
    sourceKPFinitePhase_zero_right K hζ P _
      (by simp [sourceGL2Weyl, sourceGL2Diagonal, Matrix.mul_apply, Fin.sum_univ_two])
  have hDW : sourceKPFinitePhase K hζ P (sourceGL2Diagonal u⁻¹ * sourceGL2Weyl) = 1 :=
    sourceKPFinitePhase_zero_right K hζ P _
      (by simp [sourceGL2Weyl, sourceGL2Diagonal, Matrix.mul_apply, Fin.sum_univ_two])
  have hDWS : sourceKPFinitePhase K hζ P (sourceGL2Diagonal u⁻¹ * sourceGL2Weyl * GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
    rw [← sourceGL2Weyl_mul_diagonal]
    exact hWD
  have h := sourceFiniteKP2Multiplier_weyl_diagonal K hζ P u
  exact ⟨(sourceKPFiniteTwistedMultiplier_eq_of_phase_one K hζ P _ _ (sourceKPFinitePhase_weyl K hζ P)
    (sourceKPFinitePhase_diagonal K hζ P u) hWD).trans h.1,
    (sourceKPFiniteTwistedMultiplier_eq_of_phase_one K hζ P _ _ (sourceKPFinitePhase_diagonal K hζ P u⁻¹)
      (sourceKPFinitePhase_weyl K hζ P) hDW).trans h.2.1,
    (sourceKPFiniteTwistedMultiplier_eq_of_phase_one K hζ P _ _ hDW
      (sourceKPFinitePhase_scalar K hζ P u) hDWS).trans h.2.2⟩

end
end ArtinMatthews
