module

public import ArtinMatthews.SourceKPCompactDirichletCore
public import Mathlib.Algebra.Module.TransferInstance


set_option backward.privateInPublic true
@[expose] public section

/-! The pre-Hilbert norm is the actual Haar mass plus the descended Dirichlet energy. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology InnerProductSpace ComplexConjugate
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

structure SourceKPCompactFormCore where
  val : sourceKPCompactC2Core K hζ

local notation "T" => SourceKPCompactFormCore K hζ
local notation "L" => Lp ℂ 2 (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ))
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

def sourceKPCompactFormCoreEquiv : T ≃ sourceKPCompactC2Core K hζ where
  toFun := SourceKPCompactFormCore.val
  invFun := SourceKPCompactFormCore.mk
  left_inv := fun ⟨_⟩ => rfl
  right_inv := fun _ => rfl

instance sourceKPCompactFormCoreAddCommGroup : AddCommGroup T :=
  (sourceKPCompactFormCoreEquiv K hζ).addCommGroup

def sourceKPCompactFormCoreAddEquiv : T ≃+ sourceKPCompactC2Core K hζ where
  toEquiv := sourceKPCompactFormCoreEquiv K hζ
  map_add' := fun _ _ => rfl

instance sourceKPCompactFormCoreModule : Module ℂ T :=
  (sourceKPCompactFormCoreAddEquiv K hζ).module ℂ

def sourceKPCompactFormCoreLinearEquiv : T ≃ₗ[ℂ] sourceKPCompactC2Core K hζ where
  toAddEquiv := sourceKPCompactFormCoreAddEquiv K hζ
  map_smul' := fun _ _ => rfl

def sourceKPCompactFormCoreMassLinear : T →ₗ[ℂ] L :=
  (sourceKPCompactCoreMass K hζ 2).comp (sourceKPCompactFormCoreLinearEquiv K hζ).toLinearMap

theorem sourceKPCompactFormCoreMassLinear_injective :
    Function.Injective (sourceKPCompactFormCoreMassLinear K hζ) :=
  (sourceKPCompactCoreMass_injective K hζ 2).comp (sourceKPCompactFormCoreLinearEquiv K hζ).injective

def sourceKPCompactFormCoreInner (f g : T) : ℂ :=
  inner ℂ (sourceKPCompactFormCoreMassLinear K hζ f) (sourceKPCompactFormCoreMassLinear K hζ g) +
    sourceKPCompactDirichletCore K hζ f.val g.val

theorem sourceKPCompactFormCoreInner_self (f : T) :
    (sourceKPCompactFormCoreInner K hζ f f).re =
      ‖sourceKPCompactFormCoreMassLinear K hζ f‖ ^ 2 +
        ∫ y, sourceKPCompactCoreEnergy K hζ f.val y ∂μ := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (sourceKPCompactFormCoreMassLinear K hζ f)
  change (inner ℂ (sourceKPCompactFormCoreMassLinear K hζ f)
    (sourceKPCompactFormCoreMassLinear K hζ f)).re = _ at h
  rw [sourceKPCompactFormCoreInner,sourceKPCompactDirichletCore_self,Complex.add_re,
    Complex.ofReal_re,h]

instance sourceKPCompactFormCorePreHilbert : InnerProductSpace.Core ℂ T where
  inner := sourceKPCompactFormCoreInner K hζ
  conj_inner_symm f g := by
    simp only [sourceKPCompactFormCoreInner,map_add,inner_conj_symm,
      sourceKPCompactDirichletCore_conj_symm]
  re_inner_nonneg f := by
    rw [RCLike.re_to_complex,sourceKPCompactFormCoreInner_self]
    exact add_nonneg (sq_nonneg _) (integral_nonneg (sourceKPCompactCoreEnergy_nonneg K hζ f.val))
  add_left f g h := by
    have hd :
        sourceKPCompactDirichletCore K hζ (f.val+g.val) h.val =
          sourceKPCompactDirichletCore K hζ f.val h.val +
            sourceKPCompactDirichletCore K hζ g.val h.val := by
      rw [← sourceKPCompactDirichletCore_conj_symm,sourceKPCompactDirichletCore_add_right,map_add,
        sourceKPCompactDirichletCore_conj_symm,sourceKPCompactDirichletCore_conj_symm]
    simp only [sourceKPCompactFormCoreInner,map_add,inner_add_left]
    change _ + sourceKPCompactDirichletCore K hζ (f.val+g.val) h.val = _
    rw [hd]
    abel
  smul_left f g c := by
    have hd :
        sourceKPCompactDirichletCore K hζ (c • f.val) g.val =
          conj c * sourceKPCompactDirichletCore K hζ f.val g.val := by
      rw [← sourceKPCompactDirichletCore_conj_symm,sourceKPCompactDirichletCore_smul_right,map_mul,
        sourceKPCompactDirichletCore_conj_symm]
    simp only [sourceKPCompactFormCoreInner,map_smul,inner_smul_left]
    change _ + sourceKPCompactDirichletCore K hζ (c • f.val) g.val = _
    rw [hd,mul_add]
  definite f hf := by
    have h := congrArg Complex.re hf
    change (sourceKPCompactFormCoreInner K hζ f f).re = 0 at h
    rw [sourceKPCompactFormCoreInner_self] at h
    have he : 0 ≤ ∫ y, sourceKPCompactCoreEnergy K hζ f.val y ∂μ :=
      integral_nonneg (sourceKPCompactCoreEnergy_nonneg K hζ f.val)
    have hm : ‖sourceKPCompactFormCoreMassLinear K hζ f‖ = 0 := by
      nlinarith [norm_nonneg (sourceKPCompactFormCoreMassLinear K hζ f)]
    apply sourceKPCompactFormCoreMassLinear_injective K hζ
    rw [map_zero]
    exact norm_eq_zero.mp hm

instance sourceKPCompactFormCoreNormedAddCommGroup : NormedAddCommGroup T :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance sourceKPCompactFormCoreInnerProduct : InnerProductSpace ℂ T :=
  InnerProductSpace.ofCore _

theorem sourceKPCompactFormCore_norm_sq (f : T) :
    ‖f‖ ^ 2 = ‖sourceKPCompactFormCoreMassLinear K hζ f‖ ^ 2 +
        ∫ y, sourceKPCompactCoreEnergy K hζ f.val y ∂μ := by
  have hi := inner_self_eq_norm_sq (𝕜 := ℂ) f
  change (sourceKPCompactFormCoreInner K hζ f f).re = ‖f‖ ^ 2 at hi
  rw [← hi,sourceKPCompactFormCoreInner_self]

theorem sourceKPCompactFormCoreMassLinear_norm_le (f : T) :
    ‖sourceKPCompactFormCoreMassLinear K hζ f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [sourceKPCompactFormCore_norm_sq]
  exact le_add_of_nonneg_right (integral_nonneg (sourceKPCompactCoreEnergy_nonneg K hζ f.val))

def sourceKPCompactFormCoreMass : T →L[ℂ] L :=
  (sourceKPCompactFormCoreMassLinear K hζ).mkContinuous 1 fun f => by
    simpa only [one_mul] using sourceKPCompactFormCoreMassLinear_norm_le K hζ f

end
end ArtinMatthews
