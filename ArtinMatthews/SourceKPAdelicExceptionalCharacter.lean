module

public import ArtinMatthews.SourceKPAdelicCubeTorus
public import ArtinMatthews.SourceKPTameHilbertPhase


set_option backward.privateInPublic true
@[expose] public section

/-! The actual global exceptional central character on the cube
torus. It uses the positive sixth power of the normalized idele
absolute value of the cube ratio. The cubic center has the same
inverse angular embedding as the checked local action. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AngularLambda
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicCentralComplex : rootsOfUnity 3 K →* ℂˣ :=
  (MulEquiv.inv ℂˣ).toMonoidHom.comp
    ((Units.map (sourceComplexEmbedding hζ).toMonoidHom).comp (rootsOfUnity 3 K).subtype)

theorem sourceKPAdelicCentralComplex_injective : Function.Injective (sourceKPAdelicCentralComplex K hζ) :=
  (MulEquiv.inv ℂˣ).injective.comp
    ((Units.map_injective (sourceComplexEmbedding hζ).injective).comp Subtype.val_injective)

theorem sourceKPAdelicCentralComplex_transport (P : HeightOneSpectrum (𝓞 K)) (z : rootsOfUnity 3 K) :
    sourceKPCentralComplex K hζ P (sourceKPRootsTransport K hζ P z) = sourceKPAdelicCentralComplex K hζ z := by
  let e := sourceKPRootsTransport K hζ P
  change ((Units.map (sourceComplexEmbedding hζ).toMonoidHom (e.symm (e z)).val)⁻¹ : ℂˣ) =
    (Units.map (sourceComplexEmbedding hζ).toMonoidHom z.val)⁻¹
  rw [MulEquiv.symm_apply_apply]

def sourceKPIdeleSixthNorm : IdeleGroup (𝓞 K) K →* ℂˣ where
  toFun x := Units.mk0 (((sourceKPIdeleAbsoluteNorm K x) ^ (1 / 6 : ℝ) : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (sourceKPIdeleAbsoluteNorm_pos K x) _).ne')
  map_one' := by
    apply Units.ext
    change (((sourceKPIdeleAbsoluteNorm K 1) ^ (1 / 6 : ℝ) : ℝ) : ℂ) = 1
    rw [map_one, Real.one_rpow, Complex.ofReal_one]
  map_mul' x y := by
    apply Units.ext
    change (((sourceKPIdeleAbsoluteNorm K (x * y)) ^ (1 / 6 : ℝ) : ℝ) : ℂ) =
      (((sourceKPIdeleAbsoluteNorm K x) ^ (1 / 6 : ℝ) : ℝ) : ℂ) *
      (((sourceKPIdeleAbsoluteNorm K y) ^ (1 / 6 : ℝ) : ℝ) : ℂ)
    rw [map_mul, Real.mul_rpow (sourceKPIdeleAbsoluteNorm_pos K x).le (sourceKPIdeleAbsoluteNorm_pos K y).le,
      Complex.ofReal_mul]

theorem sourceKPIdeleSixthNorm_coe (x : IdeleGroup (𝓞 K) K) :
    ((sourceKPIdeleSixthNorm K x : ℂˣ) : ℂ) =
      (((sourceKPIdeleAbsoluteNorm K x) ^ (1 / 6 : ℝ) : ℝ) : ℂ) := rfl

private def sourceKPAdelicExceptionalCharacterPair : rootsOfUnity 3 K × SourceKPIdeleCubes K →* ℂˣ where
  toFun p := sourceKPAdelicCentralComplex K hζ p.1 * sourceKPIdeleSixthNorm K p.2.val
  map_one' := by
    change sourceKPAdelicCentralComplex K hζ 1 * sourceKPIdeleSixthNorm K 1 = 1
    rw [map_one, map_one, mul_one]
  map_mul' x y := by
    change sourceKPAdelicCentralComplex K hζ (x.1 * y.1) * sourceKPIdeleSixthNorm K (x.2.val * y.2.val) = _
    rw [map_mul, map_mul]
    ac_rfl

def sourceKPAdelicExceptionalCharacter : sourceKPAdelicCubeTorus K hζ →* ℂˣ :=
  (sourceKPAdelicExceptionalCharacterPair K hζ).comp (sourceKPAdelicCubeTorusEquiv K hζ).symm.toMonoidHom

theorem sourceKPAdelicExceptionalCharacter_equiv (p : rootsOfUnity 3 K × SourceKPIdeleCubes K) :
    sourceKPAdelicExceptionalCharacter K hζ (sourceKPAdelicCubeTorusEquiv K hζ p) =
      sourceKPAdelicCentralComplex K hζ p.1 * sourceKPIdeleSixthNorm K p.2.val := by
  let E := sourceKPAdelicCubeTorusEquiv K hζ
  change sourceKPAdelicExceptionalCharacterPair K hζ (E.symm (E p)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem sourceKPAdelicExceptionalCharacter_cube (z : rootsOfUnity 3 K) (x : IdeleGroup (𝓞 K) K) :
    ((sourceKPAdelicExceptionalCharacter K hζ
      (sourceKPAdelicCubeTorusEquiv K hζ (z, sourceKPIdeleCube K x)) : ℂˣ) : ℂ) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ) *
        (((sourceKPIdeleAbsoluteNorm K x) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [sourceKPAdelicExceptionalCharacter_equiv, Units.val_mul, sourceKPIdeleSixthNorm_coe]
  change (sourceKPAdelicCentralComplex K hζ z : ℂ) *
      (((sourceKPIdeleAbsoluteNorm K (x ^ (3 : ℕ))) ^ (1 / 6 : ℝ) : ℝ) : ℂ) = _
  rw [map_pow, ← Real.rpow_natCast, ← Real.rpow_mul (sourceKPIdeleAbsoluteNorm_pos K x).le]
  rw [show ((3 : ℕ) : ℝ) * (1 / 6 : ℝ) = 1 / 2 by norm_num]

theorem sourceKPAdelicExceptionalCharacter_coroot_cube (x : IdeleGroup (𝓞 K) K) :
    ((sourceKPAdelicExceptionalCharacter K hζ
      (sourceKPAdelicCubeTorusEquiv K hζ (1, sourceKPIdeleCube K (x ^ (2 : ℕ)))) : ℂˣ) : ℂ) =
      (sourceKPIdeleAbsoluteNorm K x : ℂ) := by
  rw [sourceKPAdelicExceptionalCharacter_cube, map_one, Units.val_one, one_mul, map_pow,
    ← Real.rpow_natCast, ← Real.rpow_mul (sourceKPIdeleAbsoluteNorm_pos K x).le,
    show ((2 : ℕ) : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]

end
end ArtinMatthews
