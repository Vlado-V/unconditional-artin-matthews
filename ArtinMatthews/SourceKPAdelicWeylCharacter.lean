module

public import ArtinMatthews.SourceKPAdelicWeyl
public import ArtinMatthews.SourceKPAdelicExceptionalLocalNorm
public import ArtinMatthews.SourceKPAdelicExceptionalRational


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Weyl-conjugate exceptional central character. Its
center retains the chosen orientation and its pure cube norm
exponent is negative one-half on the underlying idele root. -/

namespace ArtinMatthews
open NumberField Matrix
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicCubeTorusWeyl : sourceKPAdelicCubeTorus K hζ ≃* sourceKPAdelicCubeTorus K hζ :=
  (sourceKPAdelicCubeTorusEquiv K hζ).symm.trans
    (((MulEquiv.refl (rootsOfUnity 3 K)).prodCongr (MulEquiv.inv (SourceKPIdeleCubes K))).trans
      (sourceKPAdelicCubeTorusEquiv K hζ))

theorem sourceKPAdelicCubeTorusWeyl_equiv (p : rootsOfUnity 3 K × SourceKPIdeleCubes K) :
    sourceKPAdelicCubeTorusWeyl K hζ (sourceKPAdelicCubeTorusEquiv K hζ p) =
      sourceKPAdelicCubeTorusEquiv K hζ (p.1, p.2⁻¹) := by
  let E := sourceKPAdelicCubeTorusEquiv K hζ
  change E (((E.symm (E p)).1), ((E.symm (E p)).2)⁻¹) = _
  rw [MulEquiv.symm_apply_apply]

theorem sourceKPAdelicCubeTorusWeyl_val (x : sourceKPAdelicCubeTorus K hζ) :
    (sourceKPAdelicCubeTorusWeyl K hζ x).val =
      sourceKPAdelicProjectiveWeyl K hζ * x.val * (sourceKPAdelicProjectiveWeyl K hζ)⁻¹ := by
  obtain ⟨p, rfl⟩ := (sourceKPAdelicCubeTorusEquiv K hζ).surjective x
  rw [sourceKPAdelicCubeTorusWeyl_equiv, sourceKPAdelicCubeTorusEquiv_val, sourceKPAdelicCubeTorusEquiv_val]
  let W := sourceKPAdelicProjectiveWeyl K hζ
  let z := sourceKPAdelicProjectiveCenter K hζ p.1
  let a := sourceKPAdelicProjectiveDiagonalLift K hζ
  change z * a p.2.val⁻¹ = W * (z * a p.2.val) * W⁻¹
  have h : Commute W z := (sourceKPAdelicProjectiveCenter_commute K hζ p.1 W).symm
  rw [h.left_comm (a p.2.val), mul_assoc z, sourceKPAdelicProjectiveWeyl_conj_diagonal]

def sourceKPAdelicWeylExceptionalCharacter : sourceKPAdelicCubeTorus K hζ →* ℂˣ :=
  (sourceKPAdelicExceptionalCharacter K hζ).comp (sourceKPAdelicCubeTorusWeyl K hζ).toMonoidHom

theorem sourceKPIdeleAbsoluteNorm_inv (x : IdeleGroup (𝓞 K) K) :
    sourceKPIdeleAbsoluteNorm K x⁻¹ = (sourceKPIdeleAbsoluteNorm K x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, inv_mul_cancel, map_one]

theorem sourceKPAdelicWeylExceptionalCharacter_cube (z : rootsOfUnity 3 K) (x : IdeleGroup (𝓞 K) K) :
    ((sourceKPAdelicWeylExceptionalCharacter K hζ
      (sourceKPAdelicCubeTorusEquiv K hζ (z, sourceKPIdeleCube K x)) : ℂˣ) : ℂ) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ) *
        (((sourceKPIdeleAbsoluteNorm K x) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
  have h : (sourceKPIdeleCube K x)⁻¹ = sourceKPIdeleCube K x⁻¹ := Subtype.ext (inv_pow x 3).symm
  change ((sourceKPAdelicExceptionalCharacter K hζ
    (sourceKPAdelicCubeTorusWeyl K hζ (sourceKPAdelicCubeTorusEquiv K hζ (z, sourceKPIdeleCube K x))) : ℂˣ) : ℂ) = _
  rw [sourceKPAdelicCubeTorusWeyl_equiv]
  change ((sourceKPAdelicExceptionalCharacter K hζ
    (sourceKPAdelicCubeTorusEquiv K hζ (z, (sourceKPIdeleCube K x)⁻¹)) : ℂˣ) : ℂ) = _
  rw [h, sourceKPAdelicExceptionalCharacter_cube, sourceKPIdeleAbsoluteNorm_inv, ← Real.rpow_neg_eq_inv_rpow]
  rw [show (-(1 / 2 : ℝ)) = -1 / 2 by ring]

theorem sourceKPAdelicWeylExceptionalCharacter_rational (g : PGL(2, K)) (x : sourceKPAdelicCubeTorus K hζ)
    (hx : sourceKPAdelicProjectiveRationalLift K hζ g = x.val) : sourceKPAdelicWeylExceptionalCharacter K hζ x = 1 := by
  let w := ProjGenLinGroup.mk (sourceKPWeylMatrix K)
  change sourceKPAdelicExceptionalCharacter K hζ (sourceKPAdelicCubeTorusWeyl K hζ x) = 1
  apply sourceKPAdelicExceptionalCharacter_rational K hζ (w * g * w⁻¹)
  rw [sourceKPAdelicCubeTorusWeyl_val, map_mul, map_mul, map_inv, hx]
  rfl

end
end ArtinMatthews
