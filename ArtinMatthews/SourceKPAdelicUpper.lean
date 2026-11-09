module

public import ArtinMatthews.SourceKPAdelicWeyl
public import ArtinMatthews.SourceKPNormalizedBorel


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical upper-root splitting in the actual c=2 cubic adelic
projective cover, and its exact agreement with the rational splitting. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

def sourceKPUpperMatrix (R : Type*) [CommRing R] (x : R) : GL (Fin 2) R :=
  GeneralLinearGroup.mk'' !![1, x; 0, 1] (by simp [Matrix.det_fin_two])

theorem sourceKPUpperMatrix_field {F : Type*} [Field F] (x : F) :
    sourceKPUpperMatrix F x = sourceGL2Upper x := by
  apply GeneralLinearGroup.ext
  intro i j
  rfl

theorem sourceKPUpperMatrix_zero (R : Type*) [CommRing R] :
    sourceKPUpperMatrix R 0 = 1 := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [sourceKPUpperMatrix]

theorem sourceKPUpperMatrix_add {R : Type*} [CommRing R] (x y : R) :
    sourceKPUpperMatrix R (x+y) = sourceKPUpperMatrix R x * sourceKPUpperMatrix R y := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceKPUpperMatrix, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem sourceKPUpperMatrix_map {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T) (x : R) :
    GeneralLinearGroup.map f (sourceKPUpperMatrix R x) = sourceKPUpperMatrix T (f x) := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [sourceKPUpperMatrix]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPFinitePhase_upper (P : HeightOneSpectrum (𝓞 K)) (x : P.adicCompletion K) :
    sourceKPFinitePhase K hζ P (sourceGL2Upper x) = 1 :=
  sourceKPFinitePhase_zero_left K hζ P _ (by simp [sourceGL2Upper])

theorem sourceKPFiniteTwistedMultiplier_upper (P : HeightOneSpectrum (𝓞 K)) (x y : P.adicCompletion K) :
    sourceKPFiniteTwistedMultiplier K hζ P (sourceGL2Upper x) (sourceGL2Upper y) = 1 := by
  have hxy : sourceGL2Upper x * sourceGL2Upper y = sourceGL2Upper (x+y) := by
    simp only [← sourceKPUpperMatrix_field, ← sourceKPUpperMatrix_add]
  rw [sourceKPFiniteTwistedMultiplier, sourceKPCochainTwist, hxy,
    sourceKPFinitePhase_upper, sourceKPFinitePhase_upper, sourceKPFinitePhase_upper,
    one_mul, one_mul, div_one]
  exact sourceKP2Multiplier_left_upper (sourceFiniteKPHilbert K hζ P) x (sourceGL2Upper y)

theorem sourceKPAdeleMatrixAt_upper (P : HeightOneSpectrum (𝓞 K)) (x : 𝔸ᶠ[K]) :
    sourceKPAdeleMatrixAt K P (sourceKPUpperMatrix 𝔸ᶠ[K] x) =
      sourceGL2Upper (x P) := by
  rw [sourceKPAdeleMatrixAt, sourceKPUpperMatrix_map, sourceKPUpperMatrix_field]
  rfl

theorem sourceKPAdeleMultiplier_upper (x y : 𝔸ᶠ[K]) :
    sourceKPAdeleMultiplier K hζ (sourceKPUpperMatrix 𝔸ᶠ[K] x) (sourceKPUpperMatrix 𝔸ᶠ[K] y) = 1 := by
  apply finprod_eq_one_of_forall_eq_one
  intro P
  rw [sourceKPAdeleLocalMultiplier, sourceKPAdeleMatrixAt_upper, sourceKPAdeleMatrixAt_upper,
    sourceKPFiniteTwistedMultiplier_upper, map_one]

def sourceKPFiniteAdeleUpperLift (x : 𝔸ᶠ[K]) : SourceKPFiniteAdeleProjective K hζ :=
  sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPUpperMatrix 𝔸ᶠ[K] x)

theorem sourceKPFiniteAdeleUpperLift_zero :
    sourceKPFiniteAdeleUpperLift K hζ 0 = 1 := by
  unfold sourceKPFiniteAdeleUpperLift sourceKPFiniteAdeleProjectiveLift
  rw [sourceKPUpperMatrix_zero]
  exact map_one (sourceKPFiniteAdeleProjectiveMk K hζ)

theorem sourceKPFiniteAdeleUpperLift_add (x y : 𝔸ᶠ[K]) :
    sourceKPFiniteAdeleUpperLift K hζ (x+y) =
      sourceKPFiniteAdeleUpperLift K hζ x * sourceKPFiniteAdeleUpperLift K hζ y := by
  unfold sourceKPFiniteAdeleUpperLift
  rw [sourceKPFiniteAdeleProjectiveLift_mul_of_phase_one K hζ _ _ (sourceKPAdeleMultiplier_upper K hζ x y),
    sourceKPUpperMatrix_add]

def sourceKPAdelicUpperLift (x : 𝔸[K]) : SourceKPAdelicProjective K hζ :=
  (ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) x.1),
    sourceKPFiniteAdeleUpperLift K hζ x.2)

theorem sourceKPAdelicUpperLift_zero :
    sourceKPAdelicUpperLift K hζ 0 = 1 := by
  apply Prod.ext
  · change ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) 0) = 1
    rw [sourceKPUpperMatrix_zero, map_one]
  · exact sourceKPFiniteAdeleUpperLift_zero K hζ

theorem sourceKPAdelicUpperLift_add (x y : 𝔸[K]) :
    sourceKPAdelicUpperLift K hζ (x+y) =
      sourceKPAdelicUpperLift K hζ x * sourceKPAdelicUpperLift K hζ y := by
  apply Prod.ext
  · change ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) (x.1+y.1)) = _
    rw [sourceKPUpperMatrix_add, map_mul]
    rfl
  · exact sourceKPFiniteAdeleUpperLift_add K hζ x.2 y.2

theorem sourceKPRationalLocalPhase_upper (x : K) (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPRationalLocalPhase K hζ (sourceGL2Upper x) P = 1 := by
  rw [sourceKPRationalLocalPhase, sourceKPAdeleMatrixAt_rational,
    ← sourceKPUpperMatrix_field, sourceKPUpperMatrix_map, sourceKPUpperMatrix_field,
    sourceKPFinitePhase_upper, map_one]

theorem sourceKPRationalLiftPhase_upper (x : K) :
    sourceKPRationalLiftPhase K hζ (sourceGL2Upper x) = 1 := by
  simp only [sourceKPRationalLiftPhase, sourceKPRationalPhaseProduct,
    sourceKPRationalLocalPhase_upper, finprod_one, inv_one]

theorem sourceKPFiniteAdeleUpperLift_rational (x : K) :
    sourceKPFiniteAdeleUpperLift K hζ (algebraMap K 𝔸ᶠ[K] x) =
      sourceKPFiniteAdeleProjectiveRationalLift K hζ (sourcePGL2Upper x) := by
  change sourceKPFiniteAdeleProjectiveMk K hζ
    ⟨1, sourceKPUpperMatrix 𝔸ᶠ[K] (algebraMap K 𝔸ᶠ[K] x)⟩ =
      sourceKPFiniteAdeleProjectiveMk K hζ (sourceKPFiniteAdeleRationalLift K hζ (sourceGL2Upper x))
  apply congrArg (sourceKPFiniteAdeleProjectiveMk K hζ)
  apply SourceKPFiniteAdeleCover.ext
  · exact (sourceKPRationalLiftPhase_upper K hζ x).symm
  · change sourceKPUpperMatrix 𝔸ᶠ[K] (algebraMap K 𝔸ᶠ[K] x) =
      GeneralLinearGroup.map (algebraMap K 𝔸ᶠ[K]) (sourceGL2Upper x)
    rw [← sourceKPUpperMatrix_field, sourceKPUpperMatrix_map]

theorem sourceKPAdelicUpperLift_rational (x : K) :
    sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x) =
      sourceKPAdelicProjectiveRationalLift K hζ (sourcePGL2Upper x) := by
  apply Prod.ext
  · change ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) (algebraMap K (InfiniteAdeleRing K) x)) =
      ProjGenLinGroup.map (algebraMap K (InfiniteAdeleRing K)) (sourcePGL2Upper x)
    rw [ProjGenLinGroup.map_mk, ← sourceKPUpperMatrix_field, sourceKPUpperMatrix_map]
  · exact sourceKPFiniteAdeleUpperLift_rational K hζ x

end
end ArtinMatthews
