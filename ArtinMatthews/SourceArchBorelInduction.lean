module

public import ArtinMatthews.SourceArchSphericalUnitary
public import ArtinMatthews.SourceAlgebraicInduction


set_option backward.privateInPublic true
@[expose] public section

/-! The actual complex projective Borel character and its induced
representation, containing the explicit spherical section. -/
namespace ArtinMatthews.SourceArchJacquet

open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

def sourceArchBorelMap : sourceGL2NormalizedBorel ℂ →* PGL(2, ℂ) :=
  ProjGenLinGroup.mk.comp (sourceGL2NormalizedBorel ℂ).subtype

def sourceArchBorel : Subgroup PGL(2, ℂ) := sourceArchBorelMap.range

theorem sourceArchBorelMap_injective : Function.Injective sourceArchBorelMap := by
  intro a b hab
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hab
  change a.val * GeneralLinearGroup.scalar (Fin 2) u = b.val at hu
  have h11 := congrArg (fun g : GL (Fin 2) ℂ => g 1 1) hu
  have ha := sourceGL2NormalizedBorel_bottom ℂ a.val a.property
  have hb := sourceGL2NormalizedBorel_bottom ℂ b.val b.property
  rw [sourceKPMatrix_right_scalar_entry] at h11
  change a.val 1 1 * (u : ℂ) = b.val 1 1 at h11
  rw [ha.2, hb.2, one_mul] at h11
  have hu1 : u = 1 := Units.ext h11
  apply Subtype.ext
  simpa only [hu1, map_one, mul_one] using hu

def sourceArchBorelEquiv : sourceGL2NormalizedBorel ℂ ≃* sourceArchBorel :=
  MulEquiv.ofBijective sourceArchBorelMap.rangeRestrict
    ⟨fun _ _ h => sourceArchBorelMap_injective (congrArg Subtype.val h),
      fun b => by
        obtain ⟨a, ha⟩ := b.property
        exact ⟨a, Subtype.ext ha⟩⟩

theorem sourceArchBorelEquiv_val (b : sourceGL2NormalizedBorel ℂ) :
    (sourceArchBorelEquiv b).val = ProjGenLinGroup.mk b.val := rfl

def sourceArchNormalizedBorelCharacter (s : ℂ) : sourceGL2NormalizedBorel ℂ →* ℂ where
  toFun b := (‖(GeneralLinearGroup.det b.val : ℂ)‖ : ℂ) ^ (2 * s + 1)
  map_one' := by simp
  map_mul' b c := by
    change (‖(GeneralLinearGroup.det (b.val * c.val) : ℂ)‖ : ℂ) ^ (2 * s + 1) = _
    rw [map_mul, Units.val_mul, norm_mul, Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _) _

def sourceArchBorelCharacter (s : ℂ) : sourceArchBorel →* ℂ :=
  (sourceArchNormalizedBorelCharacter s).comp sourceArchBorelEquiv.symm.toMonoidHom

theorem sourceArchBorelCharacter_normalized (s : ℂ) (b : sourceGL2NormalizedBorel ℂ) :
    sourceArchBorelCharacter s (sourceArchBorelEquiv b) =
      (‖(GeneralLinearGroup.det b.val : ℂ)‖ : ℂ) ^ (2 * s + 1) := by
  change sourceArchNormalizedBorelCharacter s (sourceArchBorelEquiv.symm (sourceArchBorelEquiv b)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

def sourceArchBorelRepresentation (s : ℂ) : Representation ℂ sourceArchBorel ℂ where
  toFun b := sourceArchBorelCharacter s b • (1 : Module.End ℂ ℂ)
  map_one' := by rw [map_one, one_smul]
  map_mul' b c := by
    apply LinearMap.ext
    intro z
    change sourceArchBorelCharacter s (b * c) * z =
      sourceArchBorelCharacter s b * (sourceArchBorelCharacter s c * z)
    rw [map_mul, mul_assoc]

theorem sourceArchBorelRepresentation_apply (s : ℂ) (b : sourceArchBorel) (z : ℂ) :
    sourceArchBorelRepresentation s b z = sourceArchBorelCharacter s b * z := rfl

def sourceArchInducedSpherical (s : ℂ) :
    sourceAlgebraicInducedSpace sourceArchBorel (sourceArchBorelRepresentation s) :=
  ⟨sourceArchSphericalSection s, by
    intro b g
    let a := sourceArchBorelEquiv.symm b
    have ha : sourceArchBorelEquiv a = b := sourceArchBorelEquiv.apply_symm_apply b
    rw [← ha, sourceArchBorelEquiv_val, sourceArchBorelRepresentation_apply,
      sourceArchBorelCharacter_normalized]
    induction g using ProjGenLinGroup.induction_on with
    | mk g => exact sourceArchSphericalSection_borel s a.val g a.property⟩

theorem sourceArchInducedSpherical_apply (s : ℂ) (g : PGL(2, ℂ)) :
    (sourceArchInducedSpherical s).val g = sourceArchSphericalSection s g := rfl

theorem sourceArchInducedSpherical_unitary (s : ℂ) (k : Matrix.unitaryGroup (Fin 2) ℂ) :
    sourceAlgebraicInducedRepresentation sourceArchBorel (sourceArchBorelRepresentation s)
      (sourceArchUnitaryPGL k) (sourceArchInducedSpherical s) = sourceArchInducedSpherical s := by
  apply Subtype.ext
  funext g
  exact sourceArchSphericalSection_unitary s g k

end
end ArtinMatthews.SourceArchJacquet
