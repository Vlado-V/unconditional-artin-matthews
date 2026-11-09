module

public import ArtinMatthews.SourceKPIdeleAbsoluteNorm
public import ArtinMatthews.SourceAdelicStandardHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Complex


set_option backward.privateInPublic true
@[expose] public section

/-! The archimedean component of idele dilation uses the determinant
on the actual mixed real/complex space. Complex places contribute the
square of the ordinary absolute value. -/

namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField ENNReal Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K]

local notation "X" => mixedEmbedding.mixedSpace K
local notation "A" => InfiniteAdeleRing K
local notation "E" => InfiniteAdeleRing.ringEquiv_mixedSpace K

def sourceKPArchHaarMulLinear (a : A) : X →ₗ[ℝ] X :=
  Algebra.lmul ℝ X (E a)

theorem sourceKPArchHaarMulLinear_apply (a : A) (x : X) :
    sourceKPArchHaarMulLinear K a x = E a*x := rfl

theorem sourceKPArchHaarMulLinear_abs_det (a : A) :
    |LinearMap.det (sourceKPArchHaarMulLinear K a)| = ‖a‖ := by
  let f (v : {v : InfinitePlace K // v.IsReal}) : ℝ →ₗ[ℝ] ℝ :=
    LinearMap.mulLeft ℝ ((E a).1 v)
  let g (v : {v : InfinitePlace K // v.IsComplex}) : ℂ →ₗ[ℝ] ℂ :=
    Algebra.lmul ℝ ℂ ((E a).2 v)
  have h : sourceKPArchHaarMulLinear K a =
      LinearMap.prodMap (LinearMap.pi (fun v => (f v).comp (LinearMap.proj v)))
        (LinearMap.pi (fun v => (g v).comp (LinearMap.proj v))) := by
    apply LinearMap.ext
    intro x
    rfl
  rw [h,LinearMap.det_prodMap,LinearMap.det_pi,LinearMap.det_pi,abs_mul,
    InfiniteAdeleRing.norm_def,InfinitePlace.prod_eq_prod_mul_prod]
  congr 1
  · rw [Finset.abs_prod]
    apply Finset.prod_congr rfl
    intro v _
    rw [InfinitePlace.mult_isReal v,pow_one]
    change |LinearMap.det (LinearMap.mulLeft ℝ ((E a).1 v))| = ‖a v.val‖
    rw [LinearMap.det_mulLeft,← Real.norm_eq_abs]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.property).norm_map_of_map_zero
      (map_zero _) (a v.val)
  · rw [Finset.abs_prod]
    apply Finset.prod_congr rfl
    intro v _
    rw [InfinitePlace.mult_isComplex v]
    change |Algebra.norm ℝ ((E a).2 v)| = ‖a v.val‖^2
    rw [Algebra.norm_complex_apply,Complex.normSq_eq_norm_sq,abs_of_nonneg (sq_nonneg _)]
    change ‖InfinitePlace.Completion.extensionEmbedding v.val (a v.val)‖^2 = ‖a v.val‖^2
    rw [(InfinitePlace.Completion.isometry_extensionEmbedding v.val).norm_map_of_map_zero
      (map_zero _) (a v.val)]

theorem sourceKPArchHaar_map_mul (a : Aˣ) :
    (sourceKPArchStandardHaar K).map (fun x : X => E (a : A)*x) =
      ENNReal.ofReal ‖((a⁻¹ : Aˣ) : A)‖ • sourceKPArchStandardHaar K := by
  let f := sourceKPArchHaarMulLinear K (a : A)
  have hdet : LinearMap.det f ≠ 0 := by
    intro h
    have he := sourceKPArchHaarMulLinear_abs_det K (a : A)
    change |LinearMap.det f| = _ at he
    rw [h,abs_zero] at he
    exact (sourceKPInfiniteUnit_norm_pos K a).ne' he.symm
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (sourceKPArchStandardHaar K) hdet
  change (sourceKPArchStandardHaar K).map (fun x : X => E (a : A)*x) =
    ENNReal.ofReal |(LinearMap.det f)⁻¹| • sourceKPArchStandardHaar K at h
  have ha : ‖(a : A)‖ * ‖((a⁻¹ : Aˣ) : A)‖ = 1 := by
    rw [← sourceKPInfiniteUnit_norm_mul K a a⁻¹,mul_inv_cancel]
    rw [InfiniteAdeleRing.norm_def]
    change (∏ v : InfinitePlace K, ‖(1 : v.Completion)‖ ^ v.mult) = 1
    simp
  have he : |(LinearMap.det f)⁻¹| = ‖((a⁻¹ : Aˣ) : A)‖ := by
    change |(LinearMap.det (sourceKPArchHaarMulLinear K (a : A)))⁻¹| = _
    rw [abs_inv,sourceKPArchHaarMulLinear_abs_det K (a : A)]
    symm
    apply eq_inv_of_mul_eq_one_left
    rwa [mul_comm]
  rw [he] at h
  exact h

end
end ArtinMatthews
