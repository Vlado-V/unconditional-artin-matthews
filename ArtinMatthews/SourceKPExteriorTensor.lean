module

public import ArtinMatthews.SourceKPTameCyclicWhittakerUniqueness
public import ArtinMatthews.SourceKPTameCyclicWhittakerValues
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Finite tensor products of the genuine tame cyclic representations
and their normalized Whittaker functional. The tensor action is
constructed from the actual local actions. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators TensorProduct
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (SourceExteriorPrime K S₀))

abbrev SourceKPExteriorTensor :=
  ⨂[ℂ] P : T, sourceKPTameSphericalCyclicSpace K hζ S₀ P.val

abbrev SourceKPExteriorProductGroup :=
  (P : T) → SourceFiniteKP2Projective K hζ P.val.val

def sourceKPExteriorTensorRepresentation :
    Representation ℂ (SourceKPExteriorProductGroup K hζ S₀ T) (SourceKPExteriorTensor K hζ S₀ T) where
  toFun g := PiTensorProduct.map fun P : T => sourceKPTameSphericalCyclicRepresentation K hζ S₀ P.val (g P)
  map_one' := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod]
    apply congrArg (PiTensorProduct.tprod ℂ)
    funext P
    change (sourceKPTameSphericalCyclicRepresentation K hζ S₀ P.val 1) (v P) = v P
    rw [map_one]
    rfl
  map_mul' g h := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply, PiTensorProduct.map_tprod]
    apply congrArg (PiTensorProduct.tprod ℂ)
    funext P
    change sourceKPTameSphericalCyclicRepresentation K hζ S₀ P.val (g P * h P) (v P) = _
    rw [map_mul, Module.End.mul_apply]

def sourceKPExteriorTensorSpherical : SourceKPExteriorTensor K hζ S₀ T :=
  PiTensorProduct.tprod ℂ fun P : T => sourceKPTameCyclicSphericalVector K hζ S₀ P.val

variable (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

def sourceKPExteriorTensorWhittaker : SourceKPExteriorTensor K hζ S₀ T →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ T ℂ).compLinearMap
    fun P : T => sourceKPTameCyclicWhittaker K hζ S₀ P.val hS)

theorem sourceKPExteriorTensorWhittaker_tprod
    (v : (P : T) → sourceKPTameSphericalCyclicSpace K hζ S₀ P.val) :
    sourceKPExteriorTensorWhittaker K hζ S₀ T hS (PiTensorProduct.tprod ℂ v) =
      ∏ P : T, sourceKPTameCyclicWhittaker K hζ S₀ P.val hS (v P) := by
  rw [sourceKPExteriorTensorWhittaker, PiTensorProduct.lift.tprod]
  rfl

theorem sourceKPExteriorTensorWhittaker_spherical :
    sourceKPExteriorTensorWhittaker K hζ S₀ T hS (sourceKPExteriorTensorSpherical K hζ S₀ T) = 1 := by
  rw [sourceKPExteriorTensorSpherical, sourceKPExteriorTensorWhittaker_tprod]
  simp only [sourceKPTameCyclicWhittaker_spherical, Finset.prod_const_one]

theorem sourceKPExteriorTensorWhittaker_translate (g : SourceKPExteriorProductGroup K hζ S₀ T) :
    sourceKPExteriorTensorWhittaker K hζ S₀ T hS
      (sourceKPExteriorTensorRepresentation K hζ S₀ T g (sourceKPExteriorTensorSpherical K hζ S₀ T)) =
      ∏ P : T, sourceKPTameCyclicWhittakerValue K hζ S₀ P.val hS (g P) := by
  rw [sourceKPExteriorTensorSpherical]
  change sourceKPExteriorTensorWhittaker K hζ S₀ T hS
    (PiTensorProduct.map _ (PiTensorProduct.tprod ℂ _)) = _
  rw [PiTensorProduct.map_tprod, sourceKPExteriorTensorWhittaker_tprod]
  rfl

end
end ArtinMatthews
